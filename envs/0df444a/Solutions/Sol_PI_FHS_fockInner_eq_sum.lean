-- Prove2me | solution 1 for PI.FHS.fockInner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:59.823612+00:00
-- url     : https://prove2.me/submissions/d9f69c69-9e60-4ffb-956a-0247c687a531

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PI.FHS
variable {σ : Type*}
private theorem fockInner_eq_sum_support_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  unfold FockH1Action.fockInner
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_eq_single α]
  · rw [if_pos rfl, wt]
  · intro β _ hβ
    rw [if_neg (Ne.symm hβ), mul_zero]
  · intro hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    simp only [hα, mul_zero, zero_mul]
end PI.FHS
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, coeff α P ≠ 0 → coeff α Q ≠ 0 → α ∈ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  classical
  rw [fockInner_eq_sum_support_left]
  have h1 : ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx)
    intro α _ hα
    rw [MvPolynomial.mem_support_iff, not_not] at hα
    rw [hα, map_zero, zero_mul, zero_mul]
  have h2 : ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α
      = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    apply Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx)
    intro α _ hα
    by_cases hP : coeff α P = 0
    · rw [hP, map_zero, zero_mul, zero_mul]
    · by_cases hQ : coeff α Q = 0
      · rw [hQ, mul_zero, zero_mul]
      · exact absurd (hS α hP hQ) hα
  rw [h1, h2]
end PI.FHS
