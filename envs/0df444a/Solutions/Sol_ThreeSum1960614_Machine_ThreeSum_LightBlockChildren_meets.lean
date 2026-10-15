-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:56:23.908728+00:00
-- url     : https://prove2.me/submissions/1b86bd9e-129b-4a65-9bc4-b42726955ba5

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryEnumeration_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightBlockChildren
end ThreeSum.LightBlockChildren
namespace ThreeSum.LightReportingAffine
end ThreeSum.LightReportingAffine
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
end ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference
open _root_.ThreeSum.MaskDifference


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [_root_.ThreeSum.SubsetAddress.subsetMask,_root_.ThreeSum.SubsetAddress.maskOf,_root_.ThreeSum.SubsetAddress.natPositions]









theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) := by
  have h := _root_.ThreeSum.MaskDifference.subsetMask_union_sdiff Q U hU
  have hz : (_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ)+(_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}













/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : _root_.Light.wrote μ dst f j (dst + i) = f i := by
  unfold _root_.Light.wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : _root_.Light.Outside dst j a) : _root_.Light.wrote μ dst f j a = μ a := by
  unfold _root_.Light.wrote
  rw [if_neg (by omega)]







/-! ## The tactics -/











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

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)















/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.SegN μ' b l :=
  _root_.ThreeSum1960614.Machine.Light.Seg.of_sameOutside h hs (by simpa using hd)















end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray
open _root_.ThreeSum.LightArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : _root_.ThreeSum.LightArray.SourceSafe src dst n) (hj : j < n) :
    _root_.Light.wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)











end ThreeSum.LightArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Costed affine scans used to form reporting child-prefix masks -/

namespace ThreeSum.LightReportingAffine
open _root_.ThreeSum.LightReportingAffine


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem meets {p src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : _root_.ThreeSum.LightArray.SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src,dst,n,b,c] μ (_root_.ThreeSum.LightReportingAffine.time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun i => b+c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => _root_.ThreeSum1960614.Machine.Light.wrote_done (f := fun i => b+c*μ (src+i)) hi,
      by 
          (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
             intro p2m_macro_12545772195636606797 p2m_macro_4265689903731703288
             first
             | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_4322064052873904471); (try have := p2m_macro_4322064052873904471 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_4322064052873904471)
                   intros
                   try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
             |
               (simp [] at p2m_macro_4265689903731703288;
                 ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_11945687192546809425); (try have := p2m_macro_11945687192546809425 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_11945687192546809425)
                   intros
                   try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
             | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_17476295892461720639); (try have := p2m_macro_17476295892461720639 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_17476295892461720639)
                   intros
                   try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                 fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                             its condition K x does not follow from the hypotheses.")))⟩ hw hdst rfl rfl (hT := by (first
                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingAffine.time]
                                                    first
                                                    | omega
                                                    | (ring_nf; omega))
                                                | omega
                                                |
                                                  (simp [_root_.ThreeSum.LightReportingAffine.time] <;>
                                                      first
                                                      | omega
                                                      | (ring_nf; omega)))))
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.source_read (μ := μ) (f := fun i => b+c*μ (src+i)) hsep hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega))





end ThreeSum.LightReportingAffine

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]























@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks
open _root_.ThreeSum.ReportingHostMasks


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

































theorem mask_union {W : ℕ} (S T : Finset (Fin W)) (hd : Disjoint S T) :
    _root_.ThreeSum.SubsetAddress.subsetMask (S ∪ T) = _root_.ThreeSum.SubsetAddress.subsetMask S+_root_.ThreeSum.SubsetAddress.subsetMask T := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,Finset.sum_union hd]























end ThreeSum.ReportingHostMasks

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockChildren
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets__implementation_ad2722b8f9 {pMain pEnum pAffine : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.body pEnum pAffine)) (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.Procs P pEnum pAffine)
    {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [W,h,_root_.ThreeSum.SubsetAddress.subsetMask Q,_root_.ThreeSum.SubsetAddress.subsetMask A,_root_.ThreeSum.SubsetAddress.subsetMask B,_root_.ThreeSum.SubsetAddress.subsetMask R,masks,dstL,dstR,work]
      μ (_root_.ThreeSum.LightBlockChildren.time W Q.card h)
      (fun r μ' =>
        r = (_root_.ThreeSum.SubsetAddress.subsetMask (R \ Q) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' masks ((_root_.ThreeSum.QueryCoordinates.missingSets Q h).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstL (_root_.ThreeSum.LightBlockChildren.leftMasks A Q h) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstR (_root_.ThreeSum.LightBlockChildren.rightMasks B Q h) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' masks) := by
  have hmask (S : Finset (Fin W)) : |(_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)| ≤ lim.word := by
    rw [Int.abs_natCast]
    have hs : _root_.ThreeSum.SubsetAddress.subsetMask S ≤ 2^(W+1) :=
      (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).1).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hs : (subsetMask S : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hbias : (_root_.ThreeSum.SubsetAddress.subsetMask B : ℤ)+(_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask (B ∪ Q) : ℤ) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mask_union _ _ hBQ]
    simp
  have hreturn := _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int R Q hQR
  have hAword := abs_le.mp (hmask A)
  have hBword := abs_le.mp (hmask B)
  have hQword := abs_le.mp (hmask Q)
  have hRword := abs_le.mp (hmask R)
  have hBiasWord := abs_le.mp (hmask (B ∪ Q))
  have hReturnWord := abs_le.mp (hmask (R \ Q))
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.body _root_.ThreeSum.LightBlockChildren.time
  have henum := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets (d := d+1) (μ := μ)
    (dst := masks) (work := work) C.enumBody C.weightsBody C.powersBody C.eraseBody C.recBody Q
    hw hspace hword hh (by omega) (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (henum _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen henum ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
     on_goal -1 => (rintro count μ₁ ⟨hcount, hstored, _, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (B ∪ Q) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbias, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbias, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbias, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hread₁ (i : ℕ) (hi : i < Q.card.choose h) :
      μ₁ (masks+i) = (_root_.ThreeSum.SubsetAddress.subsetMask ((_root_.ThreeSum.QueryCoordinates.missingSets Q h)[i]'(by simpa using hi)) : ℤ) := by
    have hs := hstored i (by simpa using hi)
    simpa only [List.getElem_map] using hs
  have hleftEq (i : ℕ) (hi : i < Q.card.choose h) :
      (_root_.ThreeSum.SubsetAddress.subsetMask A : ℤ)+1*μ₁ (masks+i) =
        (_root_.ThreeSum.SubsetAddress.subsetMask (A ∪ (_root_.ThreeSum.QueryCoordinates.missingSets Q h)[i]'(by simpa using hi)) : ℤ) := by
    have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₁ i hi,one_mul,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mask_union _ _ (hAQ.mono_right ht.1)]
    simp
  have hcallL := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.meets (d := d+1) (μ := μ₁)
    (src := masks) (dst := dstL) (n := Q.card.choose h) (b := (_root_.ThreeSum.SubsetAddress.subsetMask A : ℤ)) (c := 1)
    C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl hmasks))
    (by intro i hi; rw [hread₁ i hi,one_mul]; exact hmask _)
    (by intro i hi; rw [hleftEq i hi]; exact hmask _)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcallL _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcallL ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount] <;> omega)
     on_goal -1 => (rintro retL μ₂ ⟨houtL, hkeepL⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hstored₂ : _root_.ThreeSum1960614.Machine.Light.SegN μ₂ masks ((_root_.ThreeSum.QueryCoordinates.missingSets Q h).map _root_.ThreeSum.SubsetAddress.subsetMask) :=
    hstored.of_sameOutside hkeepL (Or.inl (by simpa using hmasks))
  have hread₂ (i : ℕ) (hi : i < Q.card.choose h) : μ₂ (masks+i) = μ₁ (masks+i) :=
    hkeepL _ (Or.inl (by omega))
  have hrightEq (i : ℕ) (hi : i < Q.card.choose h) :
      (_root_.ThreeSum.SubsetAddress.subsetMask (B ∪ Q) : ℤ)+(-1)*μ₂ (masks+i) =
        (_root_.ThreeSum.SubsetAddress.subsetMask (B ∪ (Q \ (_root_.ThreeSum.QueryCoordinates.missingSets Q h)[i]'(by simpa using hi))) : ℤ) := by
    have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₂ i hi,hread₁ i hi,← hbias,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.mask_union _ _ (hBQ.mono_right Finset.sdiff_subset)]
    push_cast
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int _ _ ht.1]
    ring
  have hcallR := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.meets (d := d+1) (μ := μ₂)
    (src := masks) (dst := dstR) (n := Q.card.choose h) (b := (_root_.ThreeSum.SubsetAddress.subsetMask (B ∪ Q) : ℤ)) (c := -1)
    C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl (by omega)))
    (by intro i hi; rw [hread₂ i hi,hread₁ i hi]; simpa using hmask ((_root_.ThreeSum.QueryCoordinates.missingSets Q h)[i]'(by simpa using hi)))
    (by intro i hi; rw [hrightEq i hi]; exact hmask _)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcallR _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcallR ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time, hcount] <;> omega)
     on_goal -1 => (rintro retR μ₃ ⟨houtR, hkeepR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (R \ Q) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreturn, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreturn, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreturn, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,?_,?_,?_,?_⟩
  · exact hstored₂.of_sameOutside hkeepR (Or.inl (by simp; omega))
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [_root_.ThreeSum.LightBlockChildren.leftMasks,_root_.ThreeSum1960614.Machine.Light.SegN,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] using hi
    change μ₃ (dstL+i) = _
    rw [hkeepR (dstL+i) (Or.inl (by omega)),houtL i hin,hleftEq i hin]
    simp [_root_.ThreeSum.LightBlockChildren.leftMasks]
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [_root_.ThreeSum.LightBlockChildren.rightMasks,_root_.ThreeSum1960614.Machine.Light.SegN,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] using hi
    change μ₃ (dstR+i) = _
    rw [houtR i hin,hrightEq i hin]
    simp [_root_.ThreeSum.LightBlockChildren.rightMasks]
  · intro i hi
    exact (hkeepR i (Or.inl (by omega))).trans
      ((hkeepL i (Or.inl (by omega))).trans (hkeep₁ i ⟨by omega,Or.inl hi⟩))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets__implementation_ad2722b8f9) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets__implementation_ad2722b8f9)

#print axioms solution
