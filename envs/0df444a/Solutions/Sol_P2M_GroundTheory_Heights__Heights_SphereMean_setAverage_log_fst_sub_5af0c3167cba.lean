-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:26.673968+00:00
-- url     : https://prove2.me/submissions/55660eff-7f83-400c-aca2-9814f1dce637

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_ne_top_34fed7d837d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_pos_a1becdcd33ae


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
    ⨍ y in ballSet (m + 1) 1, (log ‖y 0‖ - log (sqNorm y) / 2) = -(harmonic m : ℝ) / 2 := by
  obtain ⟨h1i, h1⟩ := integral_ballSet_neg_log_fst m
  obtain ⟨h2i, h2⟩ := integral_ballSet_neg_log_sqNorm m
  have hV : 0 < volume.real (ballSet (m + 1) 1) :=
    ENNReal.toReal_pos (volume_ballSet_one_pos _).ne' (volume_ballSet_one_ne_top _)
  have hfun : (fun y : Fin (m + 1) → ℂ => log ‖y 0‖ - log (sqNorm y) / 2) =
      fun y => (-log (sqNorm y)) / 2 - (-log ‖y 0‖) := by
    funext y
    ring
  rw [setAverage_eq, hfun, integral_sub (h2i.div_const 2) h1i, integral_div, h1, h2,
    harmonic_succ]
  push_cast
  rw [smul_eq_mul]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.SphereMean
