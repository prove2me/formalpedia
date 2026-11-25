-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_polyStep_deg_d254c2915618
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:27:45.159064+00:00
-- url     : https://prove2.me/submissions/6a0f18c5-1f62-42dd-bb39-5a2557ac6438

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_good_f0dadbd829fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_sum_eq_73cf2fba62b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
theorem _root_.solution (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by
  by_cases h0 : p.totalDegree = 0
  · left
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]; simp [polyStep, shiftPoly]
  · right
    have : (polyStep b p).totalDegree ≤ p.totalDegree - 1 := by
      rw [(sum_eq b p).2]
      refine totalDegree_finsetSum_le fun v hv => ?_
      rcases (monomial_good b v (coeff v p)).2 with h | h
      · rw [h, totalDegree_zero]; exact zero_le
      · have := monomial_le p hv; omega
    omega
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
