-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaMean_continuous_exp_qf_add_4a3dae30bfe7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:23.203935+00:00
-- url     : https://prove2.me/submissions/b686ca31-f397-4cd4-97b2-be6566a95af0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaMean

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
open Matrix Real MeasureTheory
open GroundTheory.Heights₂.Heights.KThetaMean
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KThetaMean
theorem _root_.solution (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (a : Fin g → ℝ) :
    Continuous fun x : Fin g → ℝ => exp (-c * qf Y (x + a)) := by
  have h1 : Continuous fun x : Fin g → ℝ => x + a := continuous_id.add continuous_const
  have h2 : Continuous fun x : Fin g → ℝ => qf Y (x + a) := by
    unfold qf
    exact h1.dotProduct (continuous_const.matrix_mulVec h1)
  exact (continuous_const.mul h2).rexp
end GroundTheory.Heights₂.Heights.KThetaMean
