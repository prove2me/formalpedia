-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:58.421291+00:00
-- url     : https://prove2.me/submissions/f0567257-1545-4240-a25f-79f53f139bfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5

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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by
  rw [ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le,
    abs_of_nonneg (pow_nonneg hs.le n)]
end GroundTheory.Heights₂.Heights.SphereMean
