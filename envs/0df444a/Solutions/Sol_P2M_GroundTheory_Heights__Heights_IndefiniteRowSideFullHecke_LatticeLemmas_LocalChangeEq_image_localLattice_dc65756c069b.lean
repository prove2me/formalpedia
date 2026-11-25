-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_image_localLattice_dc65756c069b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:47.622854+00:00
-- url     : https://prove2.me/submissions/eff2e7df-0fe3-4ade-921d-ac899fa65ada

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_localEquiv_toLocal_5d79f4b7f7ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt
universe u v
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
theorem _root_.solution (L : Submodule (𝓞 K) V) :
    localEquiv φ v '' (Heights.localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      (localLattice v (L.map (intEquiv φ).toLinearMap) : Set (Fin r → v.adicCompletion K)) := by
  let f := (localEquiv φ v).toLinearMap.restrictScalars (v.adicCompletionIntegers K)
  have hf : ⇑(localEquiv φ v) = ⇑f := rfl
  rw [hf, Heights.localLattice, ← Submodule.map_coe, Submodule.map_span, localLattice,
    Submodule.map_coe, Set.image_image]
  congr 2
  ext w
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, (localEquiv_toLocal φ v x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, localEquiv_toLocal φ v x⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
