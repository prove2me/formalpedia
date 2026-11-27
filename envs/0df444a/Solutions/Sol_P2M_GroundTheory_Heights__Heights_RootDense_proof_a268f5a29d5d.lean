-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDense_proof_a268f5a29d5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:08.254704+00:00
-- url     : https://prove2.me/submissions/30355625-ac2b-4990-9b93-173db52e38bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_comp_ringHom_12c3103e84a8

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RootDense
theorem _root_.solution (h₁ : MultiHomogMemCoord.Statement) (h₂ : RootsOfUnityDense.Statement) :
    RootDense.Statement := by
  intro f j m g ⟨a, ha⟩ hg
  have hQ0 : aeval (grassPolyCoord f j m) g ≠ 0 := by
    intro h0
    apply hg
    rw [grassIdeal, h₁ (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) g a ha]
    exact (RootDenseAlt.aeval_comp_ringHom
      (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) _ g).trans
      (by rw [h0, map_zero])
  let e := Fintype.equivFin (Fin f × Fin j × Fin m)
  have hP : rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g)) ≠ 0 := by
    intro h
    apply hQ0
    apply map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    apply rename_injective e e.injective
    simpa using h
  obtain ⟨z, hz, hzQ⟩ : ∃ z : Fin (Fintype.card (Fin f × Fin j × Fin m)) → ℂ,
      (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) ∧
        eval z (rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g))) ≠ 0 := by
    by_contra! H
    exact hP (h₂ _ _ H)
  refine ⟨rootPointIdeal (fun τ a b => (z ∘ e) (τ, a, b)), ⟨_, fun τ a b => hz _, rfl⟩, ?_⟩
  show g ∉ mCoordIdeal _
  rw [h₁ (Fin f) (plBlocks f j m) ℂ _ g a ha]
  refine fun h => hzQ ?_
  rw [eval_rename, eval_map, ← aeval_def, ← RootDenseAlt.aeval_rootCoord]
  exact h
end RootDense
end GroundTheory.Heights₂.Heights
