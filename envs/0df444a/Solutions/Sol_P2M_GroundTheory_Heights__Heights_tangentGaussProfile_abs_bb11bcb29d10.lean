-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:19.225509+00:00
-- url     : https://prove2.me/submissions/f757ce0d-0b36-4815-be89-8ad5f28215b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGauss_indicator_eq_3ffb47ec0d7b

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n m : ℕ) (r : ℝ) :
    tangentGaussProfile n m |r| = tangentGaussProfile n m r := by
  unfold tangentGaussProfile
  simp only [tangentGauss_indicator_eq, abs_abs]
end GroundTheory.Heights₂.Heights
