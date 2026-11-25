-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_primG_4aa3708b7524
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:18.620579+00:00
-- url     : https://prove2.me/submissions/17a653c4-d841-4c85-be9a-3ddfa38a5489

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (primG m) ((1 - s) ^ m * log s) s := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => (1 - (1 - s) ^ (m + 1)) / (m + 1)) ((1 - s) ^ m) s := by
    have := ((hasDerivAt_one_sub_pow (m + 1) s).const_sub 1).div_const ((m : ℝ) + 1)
    refine this.congr_deriv ?_
    rw [Nat.add_sub_cancel, neg_neg]
    push_cast
    field_simp
  have h2 := (h1.mul (hasDerivAt_log hs.ne')).sub (hasDerivAt_polyR m s)
  have h3 : HasDerivAt (primG m)
      ((1 - s) ^ m * log s + (1 - (1 - s) ^ (m + 1)) / (↑m + 1) * s⁻¹ - polyP m s) s := h2
  refine h3.congr_deriv ?_
  have := mul_polyP m s
  have hP : polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) * s⁻¹ := by
    rw [← this]; field_simp
  rw [hP]
  ring
end GroundTheory.Heights₂.Heights.SphereMean
