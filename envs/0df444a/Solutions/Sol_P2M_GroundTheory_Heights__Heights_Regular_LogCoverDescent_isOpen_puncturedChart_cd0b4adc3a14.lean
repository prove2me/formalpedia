-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:56.726807+00:00
-- url     : https://prove2.me/submissions/3ddfb5b3-5247-43f8-9ffb-26dbd43d57b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution : IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z | z (Fin.castLE h j) ≠ 0} := by
    ext z; simp [puncturedChart, cuspCoord]
  rw [this]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
