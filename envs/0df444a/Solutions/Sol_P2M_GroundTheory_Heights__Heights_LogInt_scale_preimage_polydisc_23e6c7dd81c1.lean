-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:58.77172+00:00
-- url     : https://prove2.me/submissions/f97643d9-a6af-4825-99cd-d2fff7e89d47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd

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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (p : ι → Prop) [DecidablePred p] (θ : ℝ) (r : ℝ) :
    scaleP p (circleMap 0 1 θ) ⁻¹' polydisc ι r = polydisc ι r := by
  ext u
  simp [polydisc, norm_scaleP_circleMap]
end GroundTheory.Heights₂.Heights.LogInt
