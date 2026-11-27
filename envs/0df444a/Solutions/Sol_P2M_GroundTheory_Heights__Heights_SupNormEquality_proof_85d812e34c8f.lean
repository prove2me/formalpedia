-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SupNormEquality_proof_85d812e34c8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:12.894929+00:00
-- url     : https://prove2.me/submissions/6849a1cd-3a5f-47a5-aad9-1f16e09dd113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VarsSubsetRangeBlockIncl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_rename_blockIncl_0286f978dfe8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_blockForm_e1c52d6b018e

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace SupNormEquality
theorem _root_.solution (hOnto : BlockSurjectivity.Statement) : SupNormEquality.Statement := by
  intro ι _ _ n P k₀ m
  refine ⟨fun f hf ↦ exists_blockForm k₀ m f hf, fun f' _ B ↦ ⟨fun h z' hz' ↦ ?_, fun h z hz ↦ ?_⟩⟩
  · rw [← hOnto ι n P k₀] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    simpa [evalCone_rename_blockIncl, projBlock] using h z hz
  · have hz' : projBlock k₀ z ∈ conePoints (P.projIdeal k₀) ℂ := by
      rw [← hOnto ι n P k₀]; exact ⟨z, hz, rfl⟩
    simpa [evalCone_rename_blockIncl, projBlock] using h _ hz'
end SupNormEquality
end GroundTheory.Heights₂.Heights
