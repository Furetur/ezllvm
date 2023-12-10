(** Use Ez module to generate LLVM IR in a easy and pleasant way. *)

(** Basic predefined common types and type making functions. *)
module Type : sig
  open Ollvm_ast

  type t = Ollvm_ast.typ

  val i1 : t
  val i32 : t
  val half : t
  val float : t
  val double : t
  val pointer : t -> t
  val vector : int -> t -> t
  val label : t
  val void : t
  val array : int -> t -> t
  val structure : t list -> t
end

(** Annotate value with their type. *)
module Value : sig
  type t = Type.t * Ollvm_ast.value
  (** [ollvm] value annotated with type its. *)

  (** Values constructors.
     Do not confound with types in Type module.
     Be careful about module inclusion/opening order
     when using both Value and Type modules. *)

  val i1 : int -> t
  val i32 : int -> t
  val half : float -> t
  val float : float -> t
  val double : float -> t
  val vector : t list -> t
  val array : t list -> t
  val structure : t list -> t
  val ident : t -> Type.t * Ollvm_ast.ident
end

(** Instruction creation. *)
module Instr : sig
  type t = Type.t * Ollvm_ast.instr
  (** [ollvm] instr annotated with its type. *)

  val call : Value.t -> Value.t list -> t
  (** [call fn args] call the function [fn] with [args] as argument. *)

  val phi : (Value.t * Value.t) list -> t
  (** [phi [(value1, label1); ... ; (valueN, labelN)]] return a value depending on
      the incoming block. [value1, ..., valueN] must have the same type. *)

  val select : Value.t -> Value.t -> Value.t -> t
  (** [select cond value_true value_false] yields [value_true] or [value_false]
      depending on the value [cond]. *)

  val alloca : ?nb:Value.t option -> ?align:int option -> Type.t -> t
  (** [alloca ty] allocates memory on the stask of current function,
      which will be automatically freed on function returns.
      Use [nb] to specify the number of values to allocate (default is one).
      Use [align] to specify the alignment option (default is None) *)

  val load : ?volatile:bool -> ?align:int option -> Value.t -> t
  (** [load ptr] yields value stored in [ptr] alloca.
      Use [align] to specify the alignment option (default is None) *)

  (* FIXME: should return instr instead of t? *)
  val store : ?volatile:bool -> ?align:int option -> Value.t -> Value.t -> t
  (** [store val ptr] store [val] in [ptr] alloca. *)

  val eq : Value.t -> Value.t -> t
  (** Int comparison. *)

  val eq : Value.t -> Value.t -> t
  val ne : Value.t -> Value.t -> t
  val ugt : Value.t -> Value.t -> t
  val uge : Value.t -> Value.t -> t
  val ult : Value.t -> Value.t -> t
  val ule : Value.t -> Value.t -> t
  val sgt : Value.t -> Value.t -> t
  val sge : Value.t -> Value.t -> t
  val slt : Value.t -> Value.t -> t
  val sle : Value.t -> Value.t -> t

  val ffalse : Value.t -> Value.t -> t
  (** Float comparison. *)

  val foeq : Value.t -> Value.t -> t
  val fogt : Value.t -> Value.t -> t
  val foge : Value.t -> Value.t -> t
  val folt : Value.t -> Value.t -> t
  val fole : Value.t -> Value.t -> t
  val fone : Value.t -> Value.t -> t
  val ord : Value.t -> Value.t -> t
  val fueq : Value.t -> Value.t -> t
  val fugt : Value.t -> Value.t -> t
  val fuge : Value.t -> Value.t -> t
  val fult : Value.t -> Value.t -> t
  val fule : Value.t -> Value.t -> t
  val fune : Value.t -> Value.t -> t
  val funo : Value.t -> Value.t -> t
  val ftrue : Value.t -> Value.t -> t

  val add : ?nsw:bool -> ?nuw:bool -> Value.t -> Value.t -> t
  (** Int binary operations. *)

  val sub : ?nsw:bool -> ?nuw:bool -> Value.t -> Value.t -> t
  val mul : ?nsw:bool -> ?nuw:bool -> Value.t -> Value.t -> t
  val udiv : ?exact:bool -> Value.t -> Value.t -> t
  val sdiv : ?exact:bool -> Value.t -> Value.t -> t
  val urem : Value.t -> Value.t -> t
  val srem : Value.t -> Value.t -> t
  val shl : ?nsw:bool -> ?nuw:bool -> Value.t -> Value.t -> t
  val lshr : ?exact:bool -> Value.t -> Value.t -> t
  val ashr : ?exact:bool -> Value.t -> Value.t -> t
  val and_ : Value.t -> Value.t -> t
  val or_ : Value.t -> Value.t -> t
  val xor : Value.t -> Value.t -> t

  val fadd : ?flags:Ollvm_ast.fast_math list -> Value.t -> Value.t -> t
  (** Float binary operations. *)

  val fsub : ?flags:Ollvm_ast.fast_math list -> Value.t -> Value.t -> t
  val fmul : ?flags:Ollvm_ast.fast_math list -> Value.t -> Value.t -> t
  val fdiv : ?flags:Ollvm_ast.fast_math list -> Value.t -> Value.t -> t
  val frem : ?flags:Ollvm_ast.fast_math list -> Value.t -> Value.t -> t

  val extractelement : Value.t -> Value.t -> t
  (** [extractelement vec idx] returns the element contained in [vec]
      at index [idx]. *)

  val insertelement : Value.t -> Value.t -> Value.t -> t
  (** [insertelement vec val idx] returns a vector whose elements ares the same as
      [vec], except the element at index [idx] which will be [val] *)

  val shufflevector : Value.t -> Value.t -> Value.t -> t

  (* Integer conversions. *)
  val trunc : Value.t -> Type.t -> t
  val zext : Value.t -> Type.t -> t
  val sext : Value.t -> Type.t -> t

  (* Float conversion *)
  val fptrunc : Value.t -> Type.t -> t
  val fpext : Value.t -> Type.t -> t
  val fptoui : Value.t -> Type.t -> t
  val fptosi : Value.t -> Type.t -> t
  val uitofp : Value.t -> Type.t -> t
  val sitofp : Value.t -> Type.t -> t

  val extractvalue : Value.t -> int list -> t
  (** [extractvalue agg idx_list] *)

  val insertvalue : Value.t -> Value.t -> int list -> t
  (** [insertvalue agg val idx_list] *)

  (** Terminators.
      A block has to finish its instruction list with a terminator.
      These constructions return a [ollvm] instruction. *)

  val br : Value.t -> Value.t -> Value.t -> Ollvm_ast.instr
  (** [br cond lbl_true lbl_false] jumps to [lbl_true] or [lbl_false]
      depending on the value of [cond]. *)

  val br1 : Value.t -> Ollvm_ast.instr
  (** [br1 label] jumps to [label]. *)

  val switch : Value.t -> Value.t -> (Value.t * Value.t) list -> Ollvm_ast.instr
  (** [switch cond default [(int1, labelN); ... ; (intN, labelN)]]
      jumps to the [labelX] whose associted [intX] is equal to [cond].
      If no such integer is found, then jumps to [default] label. *)

  val indirectbr : Value.t -> Value.t list -> Ollvm_ast.instr
  (** [indirectbr addr possibles] returns the corresponding indirectbr
      instruction. [addr] is the address where to jump, [possibles] is
      the full set of values that can take [addr]. *)

  val ret : Value.t -> Ollvm_ast.instr
  (** [ret val] returns [val]. *)

  val ret_void : Ollvm_ast.instr
  (** [ret_void] returns with no value. *)

  val assign : Value.t -> t -> Ollvm_ast.instr
  (** Binds a [t] to an identifier.
      i. e. build a [ollvm] assignment instruction. *)

  val ( <-- ) : Value.t -> t -> Ollvm_ast.instr
  (** Infix operator equivalent to [assign] function. *)

  val ignore : t -> Ollvm_ast.instr
  (** Converts a [t] into a [ollvm] instr. *)
end

(** Function and block creation. *)
module Block : sig
  type block = Ollvm_ast.ident * Ollvm_ast.instr list

  val declare : Value.t -> Type.t list -> Ollvm_ast.declaration
  (** [declare (ret_ty, fn) args_ty] declares [fn] as a function
      returning [ret_ty] and requiring arguments of types [args_ty]. *)

  val define : Value.t -> Value.t list -> block list -> Ollvm_ast.definition
  (** [define (ret_ty, fn) args instrs] defines [fn] as a function
      returning [ret_ty], with [args] as arguments and [instrs] as body. *)

  val block : Value.t -> Ollvm_ast.instr list -> block
  (** [block label instrs] binds [instrs] to [label], creating a [block]. *)
end

(** Module hanlder. *)
module Module : sig
  (** Local variable names memory. *)
  module Local : sig
    type t
    (** Abstract type of the environment *)

    val local : t -> Type.t -> string -> t * Value.t
    (** Create a local identifier (returned as a value). If a local
        variable already use [name] as identifier, it will be suffixed
        by a number in order to return a unique identifier. *)

    val empty : t
    (** The empty environment *)
  end

  type t = { m_module : Ollvm_ast.modul; m_env : Local.t }

  val init : string -> string * string * string -> string -> t
  (** [init name (arch, vendor, os) data_layout] creates a fresh module with
      name, target triple and data layout set with given parameters and
      an empty environment. *)

  val set_data_layout : t -> string -> t
  (** [set_data_layout m new_datal_layout] returns m with new_data_layout
      as data layout. Data layout specifies how data is to be laid out
      in memory. *)

  val set_target_triple : t -> string -> string -> string -> t
  (** [set_target_triple m arch vendor os] returns m with target triple
      set according to [arch vendor os] parameters. *)

  val local : t -> Type.t -> string -> t * Value.t
  (** [local m t name] returns [(m', (t, v))] where [m'] is the new
      module with new local identifier declared and [(t, v)]
      is the resulting identifier and its type. If [name <> ""],
      it will be used as identifier (possibly with a number added
      as suffix), a number will be automatically assigned otherwise. *)

  val locals : t -> Type.t -> string list -> t * Value.t list
  (** [locals m t names] return [(m', values)] where [m'] is the new
      module with new local identifiers declared and [values] is
      a list of the same length then [names] of new identifiers
      using names hint from [names] and binded to type [t]. *)

  val batch_locals : t -> (Type.t * string) list -> t * Value.t list
  (** [batch_locals m list] returns [(m', values)] where [m'] is the new
      module with new local identifiers declared and [value] is the
      list of values built with type and name hint provided by [list]. *)

  val global : t -> Type.t -> string -> t * Value.t
  (** [global m t name] returns [(m', g)] where [m'] is the new module
      resulting in the global variable [g] of name [name] and type [t]
      declaration. *)

  val declaration : t -> Ollvm_ast.declaration -> t
  (** [declaration m dc] returns [m'], which is the same module than [m],
      with [dc] declaration registered. *)

  val definition : t -> Ollvm_ast.definition -> t
  (** [definition m df] returns [m'], which is the same module than [m],
      with [df] definition registered. *)

  val lookup_declaration : t -> string -> Ollvm_ast.declaration
  (** [lookup_declaration m "foo"] looks for declaration of function
      named ["foo"] and returns it. Raises [Not_found] if ["foo"] is
      not declared. *)

  val lookup_definition : t -> string -> Ollvm_ast.definition
  (** [lookup_definition m "foo"] looks for definition of function
      named ["foo"] and returns it. Raises [Not_found] if ["foo"] is
      not defined. *)
end
