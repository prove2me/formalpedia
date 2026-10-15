-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:05.449427+00:00
-- url     : https://prove2.me/submissions/f5a44c8b-df0f-46c2-8804-f61cdb5d0078

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandLookup_search_meets
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_upperBound_hit

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BinarySearch
end ThreeSum.BinarySearch
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogLookup
end ThreeSum.LightReportingCatalogLookup
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BinarySearch
end ThreeSum1960614.Machine.ThreeSum.BinarySearch
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch
open _root_.ThreeSum.BinarySearch














theorem upperBound_correct (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    _root_.ThreeSum.BinarySearch.Partition f x n (_root_.ThreeSum.BinarySearch.upperBound f n x) := by
  apply _root_.ThreeSum.BinarySearch.upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega









end ThreeSum.BinarySearch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/





























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
namespace Emod
open _root_.Light.Emod









end Emod



















/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : _root_.Light.emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [_root_.Light.emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _


namespace Emod
open _root_.Light.Emod






variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Seg μ base (_root_.Light.powList 2 (W+1))) : _root_.ThreeSum.LightSubsetAddress.Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hs













end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum.ReportingHostPackedCatalog


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder

set_option maxHeartbeats 600000







theorem codes_length (key : ℕ → ℕ) (n : ℕ) : (_root_.ThreeSum.ReportingHostPackedCatalog.codes key n).length=n := by simp [_root_.ThreeSum.ReportingHostPackedCatalog.codes]

theorem pairKey_lt {radix left right : ℕ} (hl : left < radix) (hr : right < radix) :
    _root_.ThreeSum.ReportingHostPackedCatalog.pairKey radix left right < radix^2 := by unfold _root_.ThreeSum.ReportingHostPackedCatalog.pairKey; nlinarith



theorem packed_lt {key : ℕ → ℕ} {n i U : ℕ} (hi : i < n) (hk : key i < U) :
    _root_.ThreeSum.ReportingHostPackedCatalog.packed key n i < U*(n+1) := by unfold _root_.ThreeSum.ReportingHostPackedCatalog.packed; nlinarith

theorem packed_mod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) : _root_.ThreeSum.ReportingHostPackedCatalog.packed key n i%(n+1)=i := by
  simp [_root_.ThreeSum.ReportingHostPackedCatalog.packed,Nat.add_mod,Nat.mod_eq_of_lt (show i < n+1 by omega)]

theorem packed_emod {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℕ) : ℤ)%((n+1 : ℕ) : ℤ) = (i : ℤ) := by
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.packed_mod (key := key) hi



theorem sorted_getD_le {S : List ℤ} (hs : S.Pairwise (· ≤ ·)) :
    ∀ i j, i ≤ j → j < S.length → S.getD i 0 ≤ S.getD j 0 := by
  intro i j hij hj
  by_cases he : i=j
  · subst j; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)











end ThreeSum.ReportingHostPackedCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual logarithmic lookup of an original prefix-catalog index

The program constructs its own powers, forms the physical query pair key,
performs division-free binary search over the sorted packed records, and
uses the benchmark's binary remainder algorithm to recover the original
catalog position. No full-catalog scan or index oracle occurs.
-/

namespace ThreeSum.LightReportingCatalogLookup
open _root_.ThreeSum.LightReportingCatalogLookup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}





theorem word_components (U n A B : ℕ) :
    U ≤ 4*U+4*(n+1)+n+A+B+16 ∧ A ≤ 4*U+4*(n+1)+n+A+B+16 ∧
    n+A+16 ≤ 4*U+4*(n+1)+n+A+B+16 ∧ 4*U+4*(n+1)+16 ≤ 4*U+4*(n+1)+n+A+B+16 := by omega

theorem word_value (W n : ℕ) : _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n ≤ _root_.ThreeSum.LightReportingCatalogLookup.word W n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_components _ _ _ _).1
theorem word_power (W n : ℕ) : 2^(2*W+2) ≤ _root_.ThreeSum.LightReportingCatalogLookup.word W n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_components _ _ _ _).2.1
theorem word_search (W n : ℕ) : n+2^((2*W+1)+1)+16 ≤ _root_.ThreeSum.LightReportingCatalogLookup.word W n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_components _ _ _ _).2.2.1
theorem word_emod (W n : ℕ) : 4*_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+4*(n+1)+16 ≤ _root_.ThreeSum.LightReportingCatalogLookup.word W n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_components _ _ _ _).2.2.2









end ThreeSum.LightReportingCatalogLookup

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingCatalogLookup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program_meets__implementation_9d52b4e6c8 {μ : ℕ → ℤ} {W n src work i d : ℕ} {S : List ℤ}
    (left right : ℕ → ℕ) (hi : i < n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ work) (hpowSpace : work+(2*W+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+1)+2) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightReportingCatalogLookup.word W n : ℤ) ≤ lim.word)
    (hn : n ≤ 2^(2*W))
    (hboundL : ∀ j < n, left j < 2^W) (hboundR : ∀ j < n, right j < 2^W)
    (hunique : ∀ a < n, ∀ b < n,
      _root_.ThreeSum.ReportingHostPackedCatalog.pairKey (2^W) (left a) (right a)=_root_.ThreeSum.ReportingHostPackedCatalog.pairKey (2^W) (left b) (right b) → a=b)
    (hperm : S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey (2^W) (left j) (right j)) n))
    (hsorted : S.Pairwise (· ≤ ·)) (hseg : _root_.ThreeSum1960614.Machine.Light.Seg μ src S)
    (hd : d+2*W+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program 3 d [W,n,src,left i,right i,work] μ (_root_.ThreeSum.LightReportingCatalogLookup.time W n)
      (fun r μ' => r = (i : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by
  let key : ℕ → ℕ := fun j => _root_.ThreeSum.ReportingHostPackedCatalog.pairKey (2^W) (left j) (right j)
  let threshold : ℕ := key i*(n+1)+n
  let K := _root_.ThreeSum.BinarySearch.upperBound (fun j => S.getD j 0) n (threshold : ℤ)
  have hlen : S.length=n := hperm.length_eq.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.codes_length key n)
  have hkey : key i < 2^(2*W) := by
    simpa only [key,← pow_mul,Nat.mul_comm] using _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.pairKey_lt (hboundL i hi) (hboundR i hi)
  have hthreshold : threshold < _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n := by unfold threshold _root_.ThreeSum.LightReportingCatalogLookup.valueBound; nlinarith
  have hcode : _root_.ThreeSum.ReportingHostPackedCatalog.packed key n i < _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.packed_lt hi hkey
  have hUword : (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_value W n)).trans hword
  have hthWord : (threshold : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hthreshold.le).trans hUword
  have hcodeWord : (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hcode.le).trans hUword
  have hpowWord : ((2^(2*W+2) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_power W n)).trans hword
  have hpowBound : ∀ j ≤ 2*W+2, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hsearchWord : ((n+2^((2*W+1)+1)+16 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_search W n)).trans hword
  have hEmod : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim (n+1) (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n) work :=
    ⟨by omega,hw,by
      have hh := (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.word_emod W n)).trans hword
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh,hemodSpace⟩
  have hkeyN : key i ≤ _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n := by unfold _root_.ThreeSum.LightReportingCatalogLookup.valueBound; nlinarith
  have hmulN : 2^W*right i ≤ _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n := by unfold key _root_.ThreeSum.ReportingHostPackedCatalog.pairKey at hkeyN; omega
  have hprodN : key i*(n+1) ≤ _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n := by unfold threshold at hthreshold; omega
  have hmulZ : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hmulN : ((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hkeyZ : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ lim.word :=
    (by exact_mod_cast hkeyN : (left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ) ≤ (valueBound W n : ℤ)).trans hUword
  have hprodZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ lim.word :=
    (by exact_mod_cast hprodN :
      ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) ≤ (valueBound W n : ℤ)).trans hUword
  have hmul0 : 0 ≤ ((2^W : ℕ) : ℤ)*(right i : ℤ) := by positivity
  have hprod0 : 0 ≤ ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1) := by positivity
  have hthZ : ((left i : ℤ)+((2^W : ℕ) : ℤ)*(right i : ℤ))*((n : ℤ)+1)+(n : ℤ) ≤ lim.word := by
    simpa only [threshold,key,_root_.ThreeSum.ReportingHostPackedCatalog.pairKey,Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hthWord
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hmulZ hkeyZ hprodZ hmul0 hprod0 hthZ
  have hhit := _root_.ThreeSum.ReportingHostPackedCatalog.upperBound_hit hi hunique hperm hsorted
  change 0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ) at hhit
  have hnWidth : n < 2^(2*W+1) := by
    have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
    rw [pow_succ]
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 3) (by rfl : program[3]? = some (body 0 1 2))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.body _root_.ThreeSum.LightReportingCatalogLookup.time
  have hp := _root_.ThreeSum1960614.Machine.Light.powTable_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program) (p := 0) (d := d+1) (μ := μ)
    (dst := work) (L := 2*W+2) (b := 2) rfl hw hpowSpace hpowBound
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     on_goal -1 => (rintro powRet μ₁ ⟨hpowers, hkeepPowers⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hPowers : _root_.ThreeSum.LightSubsetAddress.Powers μ₁ work (2*W+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.powers_of_segment hpowers
  have hradius := hPowers W (by omega)
  have hradiusN : μ₁ (work+W) = ((2^W : ℕ) : ℤ) := by simpa using hradius
  have hradiusWord := hpowBound W (by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 ^ W : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hradius, hradiusN, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hradius, hradiusN, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hradius, hradiusN, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (threshold : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, threshold, key, _root_.ThreeSum.ReportingHostPackedCatalog.pairKey, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [threshold, key, _root_.ThreeSum.ReportingHostPackedCatalog.pairKey, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, threshold, key, _root_.ThreeSum.ReportingHostPackedCatalog.pairKey, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hread : ∀ j < n, μ₁ (src+j) = S.getD j 0 := by
    intro j hj
    exact (hkeepPowers _ (Or.inl (by omega))).trans (hseg.getD (by omega) 0)
  have hsort : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by
    simpa only [hlen] using _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.sorted_getD_le hsorted
  have hsearch := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandLookup.search_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program) (pSearch := 1)
    (a := src) (n := n) (powers := work) (W := 2*W+1) (x := (threshold : ℤ)) rfl μ₁
    (fun j => S.getD j 0) K hw (hsrc.trans (by omega)) (by omega) hsearchWord hread hPowers
    (_root_.ThreeSum1960614.Machine.ThreeSum.BinarySearch.upperBound_correct _ _ _ hsort) (2*W+1) 0 le_rfl (by omega)
    (by omega) (d+1) (by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsearch _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsearch ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, threshold, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [threshold, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, threshold, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     on_goal -1 => (rintro found μ₂ ⟨hfound, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  have hreadHit : μ₁ (src+(K-1)) = (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ) :=
    (hread _ (by omega)).trans hhit.2.2
  have hreadHitZ : μ₁ (((src : ℤ)+(K : ℤ)-1).toNat) = (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ) := by
    have ha : ((src : ℤ)+(K : ℤ)-1).toNat = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  have hreadHitSub : μ₁ (src+K-1) = (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ) := by
    have ha : src+K-1 = src+(K-1) := by omega
    rw [ha]
    exact hreadHit
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfound, hreadHit, hreadHitZ, hreadHitSub, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfound, hreadHit, hreadHitZ, hreadHitSub, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfound, hreadHit, hreadHitZ, hreadHitSub, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hem := _root_.ThreeSum1960614.Machine.Light.emod_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program) (p := 2) (d := d+1) (μ := μ₁)
    (x := (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ)) rfl hEmod (by simpa only [Int.abs_natCast] using (Int.ofNat_le.mpr hcode.le))
  have hemTime : _root_.Light.emodTime (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i : ℤ).natAbs (n+1) ≤
      100*(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+1)+2) := by
    have hh := _root_.ThreeSum1960614.Machine.Light.emodRounds_le (M := n+1) hcode.le
    simpa only [Int.natAbs_natCast,_root_.Light.emodTime] using
      (show 43*_root_.Light.emodRounds (_root_.ThreeSum.ReportingHostPackedCatalog.packed key n i) (n+1)+34 ≤ 100*(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+1)+2) by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hem.mono_time hemTime) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hem.mono_time hemTime) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime, _root_.ThreeSum.LightBandLookup.searchTime] <;> omega)
     on_goal -1 => (rintro index μ₃ ⟨hindex, hkeepEmod⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hindex.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.packed_emod hi),?_⟩
  intro j hj
  exact (hkeepEmod j hj).trans (hkeepPowers j (Or.inl hj))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program_meets__implementation_9d52b4e6c8) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLookup.program_meets__implementation_9d52b4e6c8)

#print axioms solution
