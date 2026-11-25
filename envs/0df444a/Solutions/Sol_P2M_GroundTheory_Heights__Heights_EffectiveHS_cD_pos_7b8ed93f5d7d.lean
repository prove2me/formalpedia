-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_cD_pos_7b8ed93f5d7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:05.751106+00:00
-- url     : https://prove2.me/submissions/cd245f19-6532-4ee9-9e39-8b6d1c983d4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution (D : ℕ) : 0 < cD D := by
  unfold cD
  have := Real.pi_pos
  positivity
end GroundTheory.Heights₂.Heights.EffectiveHS
