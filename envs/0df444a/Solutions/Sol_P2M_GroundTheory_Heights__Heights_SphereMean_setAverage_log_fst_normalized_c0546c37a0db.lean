-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_normalized_c0546c37a0db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:33.703523+00:00
-- url     : https://prove2.me/submissions/254aa5f8-ecd7-4f38-96e5-28a580d035b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2


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
theorem _root_.solution (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, log ‖((√(sqNorm y) : ℝ) : ℂ)⁻¹ * y 0‖ = -(harmonic m : ℝ) / 2 := by
  rw [← setAverage_log_fst_sub m]
  apply average_congr
  refine ae_restrict_of_ae ?_
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_fst_eq_zero m)
  filter_upwards [h0] with y hy
  have hy' : y 0 ≠ 0 := fun h => hy h
  have hs : 0 < sqNorm y := sqNorm_pos_of_ne_zero (fun h => hy' (by simp [h]))
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    log_mul (inv_ne_zero (Real.sqrt_pos.mpr hs).ne') (norm_ne_zero_iff.mpr hy'), log_inv,
    log_sqrt hs.le]
  ring
end GroundTheory.Heights₂.Heights.SphereMean
