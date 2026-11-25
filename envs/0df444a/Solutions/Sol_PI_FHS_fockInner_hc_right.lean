-- Prove2me | solution 1 for PI.FHS.fockInner_hc_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:09.552777+00:00
-- url     : https://prove2.me/submissions/d73edc0a-ae0e-478d-ba4a-124e58065aca

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
theorem _root_.solution {n : ℕ} (P Q : MvPolynomial σ ℂ) (hP : P ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner P (homogeneousComponent n Q) = FockH1Action.fockInner P Q := by
  have hP' : P.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hP
  rw [fockInner_eq_sum_support_left, fockInner_eq_sum_support_left P Q]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hP' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc
end PI.FHS
