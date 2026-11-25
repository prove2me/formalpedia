-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MixedDiffLinear_proof_c8fa9d60a210
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:42.560693+00:00
-- url     : https://prove2.me/submissions/780af039-e40e-41b4-bdb5-0217d7469f59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba

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
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace MixedDiffLinear
theorem _root_.solution : MixedDiffLinear.Statement := by
  intro K n bs f g c s b
  obtain ⟨h1, h2, h3, h4⟩ := foldr_diffStep_props (List.ofFn bs) f g c s b
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]
end MixedDiffLinear
end GroundTheory.Heights₂.Heights.NumbersDVR
