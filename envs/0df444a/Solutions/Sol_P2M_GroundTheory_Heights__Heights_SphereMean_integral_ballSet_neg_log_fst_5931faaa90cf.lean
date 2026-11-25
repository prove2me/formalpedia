-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:18.383391+00:00
-- url     : https://prove2.me/submissions/3c2c7ebb-c410-49d2-b18f-1b0f08732a39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_succ_b9dc1c063af9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_fst_b85ed1547e1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_norm_fst_le_one_2162d3b3bc0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_ne_top_34fed7d837d3


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
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log ‖x 0‖) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log ‖x 0‖ = harmonic (m + 1) / 2 * volume.real (ballSet (m + 1) 1) := by
  apply integrableOn_and_integral_of_lintegral (measurableSet_ballSet _ _)
    (volume_ballSet_one_ne_top _)
    (f := fun x : Fin (m + 1) → ℂ => -log ‖x 0‖) ((measurable_pi_apply 0).norm.log.neg)
  · intro x hx
    rw [neg_nonneg]
    exact log_nonpos (norm_nonneg _) (norm_fst_le_one hx)
  · exact div_nonneg (by exact_mod_cast (harmonic_pos (Nat.succ_ne_zero m)).le) (by norm_num)
  · rw [lintegral_ballSet_neg_log_fst, volume_ballSet_succ, ← mul_assoc, ← ENNReal.ofReal_mul
      (div_nonneg (by exact_mod_cast (harmonic_pos (Nat.succ_ne_zero m)).le) (by norm_num))]
    congr 2
    field_simp
end GroundTheory.Heights₂.Heights.SphereMean
