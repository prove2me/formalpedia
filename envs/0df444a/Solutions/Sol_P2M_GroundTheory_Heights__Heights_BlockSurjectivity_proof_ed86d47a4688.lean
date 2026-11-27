-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_proof_ed86d47a4688
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:30.701406+00:00
-- url     : https://prove2.me/submissions/1925f540-8211-4649-b66c-89374a98e026

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0

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
open MvPolynomial Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace BlockSurjectivity
theorem _root_.solution : BlockSurjectivity.Statement := by
  intro ι _ _ n P k₀
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun _ ↦ hz.1 k₀, fun f hf ↦ ?_⟩
    have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [evalCone, eval₂_rename] at h
    exact h
  · intro hw
    obtain ⟨z, hz, hzw⟩ := BlockSurjectivity.exists_point_over P k₀ w hw
    exact ⟨z, hz, funext fun u ↦ by cases u; exact hzw⟩
end BlockSurjectivity
end GroundTheory.Heights₂.Heights
