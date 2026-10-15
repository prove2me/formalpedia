-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:10.99986+00:00
-- url     : https://prove2.me/submissions/f4712c1e-4e38-4958-8059-f1fa4a89217c

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingLeaf_program_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingLeaf
end ThreeSum.LightReportingLeaf
namespace ThreeSum.LightReportingLeafBatch
end ThreeSum.LightReportingLeafBatch
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

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

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























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



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















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







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

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
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    _root_.ThreeSum.LightHistogram.count key r (i + 1) = _root_.ThreeSum.LightHistogram.count key r i + if key i = r then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]













end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets
open _root_.ThreeSum.SourceBuckets


open _root_.Finset
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000





theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    _root_.ThreeSum.SourceBuckets.offset key N (r+1) = _root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightHistogram.count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (_root_.ThreeSum.SourceBuckets.offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (_root_.ThreeSum.LightHistogram.count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    _root_.ThreeSum.LightHistogram.count key r i < _root_.ThreeSum.LightHistogram.count key r j := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    _root_.ThreeSum.SourceBuckets.offset key N M = N := by
  unfold _root_.ThreeSum.SourceBuckets.offset _root_.ThreeSum.LightHistogram.count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBuckets.offset key N r ≤ N := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_mono key N hr).trans_eq (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_total hkey)





theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < _root_.ThreeSum.SourceBuckets.offset key N (key i+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  exact Nat.add_lt_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < N :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_end hi).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (by have hk := hkey i hi; omega))

























end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf
open _root_.ThreeSum.LightReportingLeaf


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000









theorem stored_of_kept {μ ν : ℕ→ℤ} {key : ℕ→ℕ} {N Mo offsets flat stop : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N Mo offsets flat) (hkey : ∀ i<N, key i<Mo)
    (hoffsets : offsets+Mo+1≤ stop) (hflat : flat+N≤ stop) (hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν stop) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored ν key N Mo offsets flat := by
  constructor
  · intro r hr
    exact (hkeep _ (by omega)).trans (H.offsets r hr)
  · intro i hi
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_lt hkey hi
    exact (hkeep _ (by omega)).trans (H.indices i hi)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch
open _root_.ThreeSum.LightReportingLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000



theorem hit_succ (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (NL NR Mo n : ℕ) :
    _root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) ↔
      _root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n ∨
      _root_.ThreeSum.LightReportingLeaf.Hit a (xL n) (xR n) left right keyL keyR NL NR Mo (flagL n) (flagR n) := by
  constructor
  · rintro ⟨i,hi,hh⟩
    by_cases hin : i<n
    · exact Or.inl ⟨i,hin,hh⟩
    · have he : i=n := by omega
      exact Or.inr (he ▸ hh)
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨n,by omega,hh⟩









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightReportingLeafBatch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingLeafBatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open scoped _root_.BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets__implementation_a7bac9a469 {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : ℕ}
    (a : ℤ) (xL xR left right : ℕ→ℤ) (keyL keyR flagL flagR : ℕ→ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL Mo offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+4≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hrawL : rawL+n≤work) (hrawR : rawR+n≤work)
    (hflagsL : flagsL+n≤work) (hflagsR : flagsR+n≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : ∀ i<n, flagL i≤1) (hflagR : ∀ i<n, flagR i≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadXL : ∀ i<n, μ (rawL+i)=xL i) (hreadXR : ∀ i<n, μ (rawR+i)=xR i)
    (hreadFL : ∀ i<n, μ (flagsL+i)=(flagL i : ℤ))
    (hreadFR : ∀ i<n, μ (flagsR+i)=(flagR i : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : ∀ i<n, |xL i|≤(U : ℤ)) (hxR : ∀ i<n, |xR i|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program 6 d [a,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,Mo,rawL,rawR,flagsL,flagsR,n,work]
      μ (_root_.ThreeSum.LightReportingLeafBatch.time keyL keyR flagL flagR NL NR Mo U xL xR n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν work) := by
  have haBounds := abs_le.mp ha
  induction n generalizing μ d with
  | zero =>
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.body _root_.ThreeSum.LightReportingLeafBatch.time
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · omega
      · (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
           try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
        exact ⟨by simp,by simp [_root_.ThreeSum.LightReportingLeafBatch.Hit],_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
  | succ n ih =>
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 6) (by rfl : program[6]?=some (body 6 5))
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.body
      rw [_root_.ThreeSum.LightReportingLeafBatch.time]
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < ((n + 1 : ℕ) : ℤ)) (fun hyes => ?_) (fun hbad => ?_) ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · have hrun := ih (μ := μ) (d := d+1) HL HR (by omega)
          (by omega) (by omega) (by omega) (by omega)
          (fun i hi => hflagL i (by omega)) (fun i hi => hflagR i (by omega))
          hreadL hreadR (fun i hi => hreadXL i (by omega)) (fun i hi => hreadXR i (by omega))
          (fun i hi => hreadFL i (by omega)) (fun i hi => hreadFR i (by omega))
          (fun i hi => hxL i (by omega)) (fun i hi => hxR i (by omega))
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
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
           on_goal -1 => (rintro prev ν ⟨hprevBool, hprev, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        have HLν := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
        have HRν := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
        have hxL' := abs_le.mp (hxL n (by omega))
        have hxR' := abs_le.mp (hxR n (by omega))
        have hfL := hflagL n (by omega)
        have hfR := hflagR n (by omega)
        have hXL : ν (rawL+n)=xL n := (hkeep _ (by omega)).trans (hreadXL n (by omega))
        have hXR : ν (rawR+n)=xR n := (hkeep _ (by omega)).trans (hreadXR n (by omega))
        have hFL : ν (flagsL+n)=(flagL n : ℤ) := (hkeep _ (by omega)).trans (hreadFL n (by omega))
        have hFR : ν (flagsR+n)=(flagR n : ℤ) := (hkeep _ (by omega)).trans (hreadFR n (by omega))
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
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
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (xL n) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hXL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hXL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hXL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
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
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (xR n) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hXR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hXR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hXR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
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
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (flagL n : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hFL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hFL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hFL, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
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
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (flagR n : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hFR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hFR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hFR, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
           try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
        have hleaf := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program_meets (μ := ν) (d := d+1) (srcL := srcL) (srcR := srcR)
          a (xL n) (xR n) left right keyL keyR HLν HRν hw (by omega) hMo
          hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hspace hword hkeyL hkeyR hfL hfR
          (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
          (fun i hi => (hkeep _ (by omega)).trans (hreadR i hi))
          hvaluesL hvaluesR ha htarget (hxL n (by omega)) (hxR n (by omega)) hcountWord).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.body 6 5]
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
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hleaf _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hleaf ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
           on_goal -1 => (rintro found ν₂ ⟨hfoundBool, hfound, hkeepLeaf⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with h | h <;> omega
        have hfoundRange : 0≤found ∧ found≤1 := by rcases hfoundBool with h | h <;> omega
        have hwhole : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₂ work := fun i hi => (hkeepLeaf i hi).trans (hkeep i hi)
        have hsum : (0 : ℤ)<prev+found ↔ _root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) := by
          rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.hit_succ]
          rw [show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < prev + found) (fun hfoundSome => ?_) (fun hfoundNone => ?_) ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
           all_goals
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
        · have htrue := hsum.mp hfoundSome
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
             try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
          exact ⟨by simp,by simpa using htrue,hwhole⟩
        · have hfalse : ¬_root_.ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo (n+1) :=
            fun hh => hfoundNone (hsum.mpr hh)
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingLeaf.time, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
             try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
          exact ⟨by simp,by simp [hfalse],hwhole⟩
      · omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets__implementation_a7bac9a469) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingLeafBatch.program_meets__implementation_a7bac9a469)

#print axioms solution
