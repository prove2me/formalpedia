-- Prove2me | solution 1 for PI.FHS.fockInner_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:36.906601+00:00
-- url     : https://prove2.me/submissions/c7ba580e-bd29-4ab3-99e7-5a8c99cdbcfa

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_conj_wt
import Theorems.Thm_PI_FHS_fockInner_eq_sum_right
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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) :
    (starRingEnd ℂ) (FockH1Action.fockInner Q P) = FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right Q P P.support (Finset.Subset.refl _),
    fockInner_eq_sum_support_left P Q, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, map_mul, conj_wt, Complex.conj_conj]
  ring
end PI.FHS
