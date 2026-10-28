-- Prove2me | solution 1 for ThreeBoundConditional.strictOutBits_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:44:12.227517+00:00
-- url     : https://prove2.me/submissions/62a16fba-6a5c-4e1f-80c9-8ea839df14f8

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_StrictPositive
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]















theorem rejects_of_le (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : I → Bool) (hi : F i x = false) : F j x = false := by
  cases hj : F j x with
  | false => rfl
  | true => have hh := hF i j hij x hj; rw [hi] at hh; contradiction

















































end
end ThreeBoundProfiles






end

section
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






end

section
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]













@[simp] theorem mem_guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v w : V) :
    w ∈ guardFailures S F g x v ↔ S.Adj v w ∧ F g (child x w (S.label v w)) = true := by
  simp [guardFailures]





























































end
end ThreeBoundConditional




end

section
/- Strict conditional union transfer for actual Boolean rows and parents. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem zero_row_guard_false (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V)
    (hv : ordinaryRow S F t g 0 x v) (w : V) (hvw : S.Adj v w) :
    F g (child x w (S.label v w)) = false := by
  have hempty : guardFailures S F g x v = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hv.2)
  cases hf : F g (child x w (S.label v w)) with
  | false => rfl
  | true =>
    have hm := (mem_guardFailures S F g x v w).2 ⟨hvw,hf⟩
    rw [hempty] at hm
    exact False.elim (Finset.notMem_empty _ hm)



































end
end ThreeBoundConditional



end

section
/- Refined strict conditional positive transfer, including source-labeled cap. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]





theorem strictOutHeads_other_true (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L) (hgt : gj ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (v : V) (hv : v ∈ strictOutHeads S F tl gl x p) (c : Bool) (hc : c ≠ S.label p v) :
    F tl (child x v c)=true := by
  obtain ⟨_,hR,c₀,hfalse,hother,hgl⟩ := Finset.mem_filter.mp hv
  have hz := zero_row_guard_false S F tj gj x p hp v hR
  have htl : F tl (child x v (S.label p v))=false := rejects_of_le F hF gj tl hgt _ hz
  have he : S.label p v=c₀ := by
    by_contra hn
    have hh := hother _ hn
    rw [htl] at hh
    contradiction
  exact hother c (by simpa only [← he] using hc)

theorem strictOutHeads_card (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hglt : gl ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (cap : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1)) :
    (strictOutHeads S F tl gl x p).card ≤ cap := by
  classical
  let A := strictOutHeads S F tl gl x p
  have hdis : Disjoint A {p} := by
    apply Finset.disjoint_left.mpr
    intro v hv hpv
    have he : v=p := Finset.mem_singleton.mp hpv
    subst v
    exact S.loopless p (Finset.mem_filter.mp hv).2.1
  have hdom : ∀ v ∈ ({p} : Finset V), ∀ w ∈ A, S.Adj v w := by
    intro v hv w hw
    have he : v=p := Finset.mem_singleton.mp hv
    subst v
    exact (Finset.mem_filter.mp hw).2.1
  have hzero : ∀ v ∈ A ∪ {p},
      (CandidateCoherence.mismatch S.Adj S.label A (S.label p) v).card=0 := by
    intro v hv
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwA,hR,hne⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_union.mp hv with hvA | hvp
    · obtain ⟨_,_,c₀,hfalse,hother,hgl⟩ := Finset.mem_filter.mp hvA
      have htrue := hF _ _ hglt _
        (strictOutHeads_other_true S F hF tj gj tl gl hgt x p hp w hwA (S.label v w) hne)
      have hmem := (mem_guardFailures S F gl x v w).2 ⟨hR,htrue⟩
      rw [hgl] at hmem
      exact Finset.notMem_empty _ hmem
    · have he : v=p := Finset.mem_singleton.mp hvp
      subst v
      exact hne rfl
  have hh := hcap A {p} (S.label p) hdis (by simp) hdom hzero
  change A.card ≤ cap
  omega





























end
end ThreeBoundConditional




end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem solution (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (tj gj tl gl : L)
    (hgt : gj ≤ tl) (hglt : gl ≤ tl)
    (x : ((V × Bool) × I) → Bool) (p : V) (hp : ordinaryRow S F tj gj 0 x p)
    (cap a : ℕ) (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (cap+1))
    (ha : ABound F gj tl a) : (strictOutBits S F tl gl x p).card ≤ cap*a := by
  calc
    _ ≤ ∑ v ∈ strictOutHeads S F tl gl x p,
      (liftBits v (S.label p v) (flipsTo (F tl) true (child x v (S.label p v)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ strictOutHeads S F tl gl x p, a := by
      apply Finset.sum_le_sum
      intro v hv
      rw [card_liftBits]
      exact ha _ (zero_row_guard_false S F tj gj x p hp v (Finset.mem_filter.mp hv).2.1)
    _ ≤ cap*a := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      simpa using Nat.mul_le_mul_right a (strictOutHeads_card S F hF tj gj tl gl hgt hglt x p hp cap hcap)
end
