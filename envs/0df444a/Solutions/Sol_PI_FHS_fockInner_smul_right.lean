-- Prove2me | solution 1 for PI.FHS.fockInner_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:17.440342+00:00
-- url     : https://prove2.me/submissions/1f7be190-38ae-4c6d-bd01-e708943fda4a

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
theorem _root_.solution (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul]
  ring
end PI.FHS
