-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:14:59.479804+00:00
-- url     : https://prove2.me/submissions/15b80521-b171-4c6b-9a23-9631d300b17c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_add__16b64fda1f31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128

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
theorem _root_.solution (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, diffStep_add']
    · rw [h2, diffStep_smul']
    · rw [h3, diffStep_shiftFn']
    · rw [h4, diffStep_comm']
end GroundTheory.Heights₂.Heights.NumbersDVR
