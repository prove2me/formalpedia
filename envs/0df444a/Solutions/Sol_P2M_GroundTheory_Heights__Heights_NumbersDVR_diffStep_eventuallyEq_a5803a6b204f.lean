-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:43.464662+00:00
-- url     : https://prove2.me/submissions/7af242a6-73f4-4a55-a359-70e3ec937c54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTClosure
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f

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
theorem _root_.solution (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']
end GroundTheory.Heights₂.Heights.NumbersDVR
