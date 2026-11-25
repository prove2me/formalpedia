-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BallAverageLinear_ballH_eq_preimage_917609adca6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:17.71446+00:00
-- url     : https://prove2.me/submissions/e05e7626-4706-44fd-9375-8654f57a7dd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBallAverageLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d

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
open MeasureTheory Measure Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.BallAverageLinear
namespace GroundTheory.Heights₂.Heights.BallAverageLinear
theorem _root_.solution {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by
  ext v
  simp [ballH, HermNorm.norm, HermNorm.std, matEquiv_apply]
end GroundTheory.Heights₂.Heights.BallAverageLinear
