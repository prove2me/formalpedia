-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:48.568743+00:00
-- url     : https://prove2.me/submissions/691f444e-931f-460f-ac0d-ca1212d3d37e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {D : ℕ} (u : Circle) :
    MeasurePreserving (fun z : Fin D → ℂ => (u : ℂ) • z) := by
  have h := volume_preserving_pi (fun _ : Fin D => (rotation u).measurePreserving)
  convert h using 1
  funext z j
  simp [rotation_apply]
end GroundTheory.Heights₂.Heights.HilbertSamuel
