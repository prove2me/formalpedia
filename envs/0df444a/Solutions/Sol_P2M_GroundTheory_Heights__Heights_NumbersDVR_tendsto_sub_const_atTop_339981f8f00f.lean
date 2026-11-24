-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:21.061083+00:00
-- url     : https://prove2.me/submissions/d42b251a-8624-42e4-b860-edcc2c79de28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id
end GroundTheory.Heights₂.Heights.NumbersDVR
