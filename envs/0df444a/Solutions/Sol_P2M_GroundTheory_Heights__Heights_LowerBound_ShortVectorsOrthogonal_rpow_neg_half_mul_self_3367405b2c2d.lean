-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_ShortVectorsOrthogonal_rpow_neg_half_mul_self_3367405b2c2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:37.325024+00:00
-- url     : https://prove2.me/submissions/ea355a89-fa37-49e0-92c6-c7fa8b07ec57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PShortVectorsOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace ShortVectorsOrthogonal
theorem _root_.solution {vr : ℝ} (hvr : 0 < vr) :
    vr ^ (-(1 / 2 : ℝ)) * vr ^ (-(1 / 2 : ℝ)) = vr⁻¹ := by
  rw [← Real.rpow_add hvr]
  norm_num [Real.rpow_neg_one]
end ShortVectorsOrthogonal
end GroundTheory.Heights₂.Heights.LowerBound
