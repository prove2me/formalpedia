-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:32.10526+00:00
-- url     : https://prove2.me/submissions/ce15e762-b57b-47b7-b951-7c9469dcf46a

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketTest_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBuckets_Stored_mem_bucketList

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingBucketPairs
end ThreeSum.LightReportingBucketPairs
namespace ThreeSum.LightReportingBucketRow
end ThreeSum.LightReportingBucketRow
namespace ThreeSum.LightReportingBucketTest
end ThreeSum.LightReportingBucketTest
namespace ThreeSum.LightReportingLeaf
end ThreeSum.LightReportingLeaf
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
end ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
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







/-! ## The limits -/









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
# Exact original-value testing of one retained physical bucket

The procedure visits the bucket's physical index array and reads the original
value at each index. It counts exact integer equalities with the supplied
target and preserves every memory cell. Equal values at distinct original
indices remain separate tests.
-/

namespace ThreeSum.LightReportingBucketRow
open _root_.ThreeSum.LightReportingBucketRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000









theorem count_pos_iff (target : ℤ) (value : ℕ → ℤ) (index : ℕ → ℕ) (n : ℕ) :
    0 < _root_.ThreeSum.LightReportingBucketRow.count target value index n ↔ ∃ j < n, value (index j)=target := by
  simp [_root_.ThreeSum.LightReportingBucketRow.count,Finset.card_pos,Finset.Nonempty]








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h







theorem emodTime_le {x : ℤ} {p U : ℕ} (hx : |x| ≤ (U : ℤ)) :
    _root_.Light.emodTime x.natAbs p ≤ _root_.ThreeSum.LightResidues.residueBudget U := by
  have hU : x.natAbs ≤ U := by simpa only [← Int.natCast_natAbs, Nat.cast_le] using hx
  have h := _root_.ThreeSum1960614.Machine.Light.emodRounds_le (M := p) hU
  unfold _root_.Light.emodTime _root_.ThreeSum.LightResidues.residueBudget
  omega







end ThreeSum.LightResidues

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
# Exact original-value testing of a retained Cartesian bucket pair

Every pair of retained physical indices is tested using the original integer
arrays. The result counts exactly the pairs with `a+b=c`. An empty right
fiber skips the entire left scan, so the verified cost is linear in the
actual Cartesian pair mass plus one, including empty fibers.
-/

namespace ThreeSum.LightReportingBucketPairs
open _root_.ThreeSum.LightReportingBucketPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000











theorem count_pos_iff (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    0 < _root_.ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL ↔
      ∃ i < nL, ∃ j < nR, right (indexR j)-left (indexL i)-a=0 := by
  rw [_root_.ThreeSum.LightReportingBucketPairs.count,Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_range,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.count_pos_iff]
  constructor
  · rintro ⟨i,hi,j,hj,he⟩
    exact ⟨i,hi,j,hj,by omega⟩
  · rintro ⟨i,hi,j,hj,he⟩
    exact ⟨i,hi,j,hj,by omega⟩










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightReportingBucketPairs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Physical bucket-test semantics and original-index completeness

The selected offset segment contains exactly the original physical indices
in one residue fiber, with an independent endpoint flag. The literal pair
tester therefore recognizes exactly the compatible original value pairs.
-/

namespace ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum.ReportingHostBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000









theorem exists_index_iff {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag i : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hkey : ∀ i < N, key i<M) (hr : r<M) :
    (∃ j<_root_.ThreeSum.LightSourceBucketSelect.countSelected key N r flag, _root_.ThreeSum.ReportingHostBucketTest.index μ flat key N r j=i) ↔
      flag=1 ∧ i<N ∧ key i=r := by
  by_cases hf : flag=1
  · simp only [_root_.ThreeSum.LightSourceBucketSelect.countSelected,hf,ite_true,true_and]
    rw [← H.mem_bucketList hkey hr]
    simp only [_root_.ThreeSum.SourceBuckets.bucketList,List.mem_ofFn]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨⟨j,hj⟩,he⟩
    · rintro ⟨j,he⟩
      exact ⟨j.val,j.isLt,he⟩
  · simp [_root_.ThreeSum.LightSourceBucketSelect.countSelected,hf]





theorem testCount_pos_iff {μ : ℕ → ℤ} {keyL keyR : ℕ → ℕ}
    {NL NR M offsetsL offsetsR flatL flatR rL rR flagL flagR : ℕ}
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (a : ℤ) (left right : ℕ → ℤ) :
    0<_root_.ThreeSum.ReportingHostBucketTest.testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR ↔
      flagL=1 ∧ flagR=1 ∧
        ∃ i<NL, ∃ j<NR, keyL i=rL ∧ keyR j=rR ∧ right j-left i-a=0 := by
  rw [_root_.ThreeSum.ReportingHostBucketTest.testCount,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.count_pos_iff]
  constructor
  · rintro ⟨i,hi,j,hj,he⟩
    obtain ⟨hfL,hiL,hki⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.exists_index_iff HL hkeyL hrL).mp ⟨i,hi,rfl⟩
    obtain ⟨hfR,hjR,hkj⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.exists_index_iff HR hkeyR hrR).mp ⟨j,hj,rfl⟩
    exact ⟨hfL,hfR,_,hiL,_,hjR,hki,hkj,he⟩
  · rintro ⟨hfL,hfR,i,hi,j,hj,hki,hkj,he⟩
    obtain ⟨s,hs,hes⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.exists_index_iff HL hkeyL hrL).mpr ⟨hfL,hi,hki⟩
    obtain ⟨t,ht,het⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.exists_index_iff HR hkeyR hrR).mpr ⟨hfR,hj,hkj⟩
    exact ⟨s,hs,t,ht,by simpa only [hes,het] using he⟩

end ThreeSum.ReportingHostBucketTest

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest
open _root_.ThreeSum.LightReportingBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem program_meets {srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ} (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2≤lim.depth)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+M+1≤work) (hoffsetsR : offsetsR+M+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work) (hspace : work+4≤lim.space)
    (hkeyL : ∀ i<NL, keyL i<M) (hkeyR : ∀ j<NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.program 3 d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (_root_.ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(_root_.ThreeSum.ReportingHostBucketTest.testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν work 4) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets rfl rfl rfl rfl a left right keyL keyR HL HR hw hd hsrcL hsrcR hoffsetsL hoffsetsR
    hflatL hflatR hspace hkeyL hkeyR hrL hrR hflagL hflagR hreadL hreadR hvaluesL hvaluesR ha htarget hcountWord



end ThreeSum.LightReportingBucketTest

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingLeaf
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf

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
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program_meets__implementation_0fac616771 {μ : ℕ→ℤ}
    {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo flagL flagR work U d : ℕ}
    (a xL xR : ℤ) (left right : ℕ→ℤ) (keyL keyR : ℕ→ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL Mo offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR Mo offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3≤lim.depth) (hMo : 0<Mo)
    (hsrcL : srcL+NL≤work) (hsrcR : srcR+NR≤work)
    (hoffsetsL : offsetsL+Mo+1≤work) (hoffsetsR : offsetsR+Mo+1≤work)
    (hflatL : flatL+NL≤work) (hflatR : flatR+NR≤work)
    (hspace : work+4+(Nat.log 2 (U+1)+2)≤lim.space)
    (hword : (4*U+4*Mo+16 : ℤ)≤lim.word)
    (hkeyL : ∀ i<NL, keyL i<Mo) (hkeyR : ∀ j<NR, keyR j<Mo)
    (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i<NL, |a+left i|≤lim.word)
    (hxL : |xL|≤(U : ℤ)) (hxR : |xR|≤(U : ℤ))
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program 5 d [a,srcL,srcR,offsetsL,flatL,xL,flagL,offsetsR,flatR,xR,flagR,NL,NR,Mo,work]
      μ (_root_.ThreeSum.LightReportingLeaf.time keyL keyR NL NR Mo flagL flagR U xL xR)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.LightReportingLeaf.Hit a xL xR left right keyL keyR NL NR Mo flagL flagR) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν work) := by
  have hpre : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo U (work+4) := ⟨hMo,hw,hword,hspace⟩
  have htimeL := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := Mo) hxL
  have htimeR := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.emodTime_le (p := Mo) hxR
  unfold _root_.Light.emodTime _root_.ThreeSum.LightResidues.residueBudget at htimeL htimeR
  have hlog : Nat.log 2 (1+U)=Nat.log 2 (U+1) := by rw [Nat.add_comm]
  have hlLt := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hMo 1 xL
  have hrLt := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hMo 1 xR
  have hlCast := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hMo 1 xL
  have hrCast := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hMo 1 xR
  simp only [one_mul] at hlCast hrCast
  have haBounds := abs_le.mp ha
  have hxLBounds := abs_le.mp hxL
  have hxRBounds := abs_le.mp hxR
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 5) (by rfl : program[5]?=some (body 4 3))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.body _root_.ThreeSum.LightReportingLeaf.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program) (p := 4) (x := xL) rfl hpre hxL) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program) (p := 4) (x := xL) rfl hpre hxL) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     on_goal -1 => (rintro l ν₁ ⟨hl, hkeepL⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [← hlCast] at hl
  subst l
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.emod_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program) (p := 4) (x := xR) rfl hpre hxR) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.emod_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program) (p := 4) (x := xR) rfl hpre hxR) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨hr, hkeepR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [← hrCast] at hr
  subst r
  have hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₂ work := fun i hi =>
    (hkeepR i (by omega)).trans (hkeepL i (by omega))
  have HL₂ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
  have HR₂ := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
  have htest := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.program_meets (d := d+1) (μ := ν₂)
    (srcL := srcL) (srcR := srcR) (work := work) a left right keyL keyR HL₂ HR₂ hw (by omega)
    hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR (by omega) hkeyL hkeyR hlLt hrLt hflagL hflagR
    (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
    (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj))
    hvaluesL hvaluesR ha htarget hcountWord).append [_root_.ThreeSum1960614.Machine.Light.emodBody,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.body 4 3]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (htest _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen htest ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     on_goal -1 => (rintro found ν₃ ⟨hfound, hkeepTest⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hwhole : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₃ work := fun i hi =>
    (hkeepTest i (Or.inl hi)).trans (hkeep i hi)
  have hhit : (0 : ℤ)<found ↔ _root_.ThreeSum.LightReportingLeaf.Hit a xL xR left right keyL keyR NL NR Mo flagL flagR := by
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.testCount_pos_iff (rL := _root_.ThreeSum.LightResidues.residue Mo 1 xL) (rR := _root_.ThreeSum.LightResidues.residue Mo 1 xR)
      (flagL := flagL) (flagR := flagR) HL₂ HR₂ hkeyL hkeyR hlLt hrLt a left right
    change _ ↔ _root_.ThreeSum.LightReportingLeaf.Hit a xL xR left right keyL keyR NL NR Mo flagL flagR at hpos
    rw [hfound]
    constructor
    · intro hh
      exact hpos.mp (by omega)
    · intro hh
      have hh' := hpos.mpr hh
      omega
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < found) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have htrue := hhit.mp hyes
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp,by simpa using htrue,hwhole⟩
  · have hfalse : ¬_root_.ThreeSum.LightReportingLeaf.Hit a xL xR left right keyL keyR NL NR Mo flagL flagR :=
      fun hh => hno (hhit.mpr hh)
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightReportingBucketTest.time, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp,by simp [hfalse],hwhole⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program_meets__implementation_0fac616771) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingLeaf.program_meets__implementation_0fac616771)

#print axioms solution
