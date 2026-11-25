-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:26.542303+00:00
-- url     : https://prove2.me/submissions/61d20308-1e93-4d1f-94b5-0227c0b9f852

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive

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
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.KernelPositive
namespace GroundTheory.Heights₂.Heights.Regular.KernelPositive
theorem _root_.solution {n : ℕ} (z : Fin n → ℂ) (t : ℂ) (k : Fin n) : line z t k = z k + t := by
  simp [line]
end GroundTheory.Heights₂.Heights.Regular.KernelPositive
