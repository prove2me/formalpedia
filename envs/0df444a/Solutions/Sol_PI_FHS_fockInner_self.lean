-- Prove2me | solution 1 for PI.FHS.fockInner_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:40.441497+00:00
-- url     : https://prove2.me/submissions/dc4a350a-6213-4254-afd4-c7ca97d7a4d4

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_wt_eq_nat
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
private theorem conj_mul_self_eq_normSq (z : ℂ) : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm
end PI.FHS
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P P =
    ∑ α ∈ P.support, (((Complex.normSq (coeff α P)) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_sum_support_left]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [conj_mul_self_eq_normSq, wt_eq_nat]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast]
end PI.FHS
