-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_aAt_of_bAt_bab6f562c0e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:31.335849+00:00
-- url     : https://prove2.me/submissions/1bb6c041-7093-40ee-8743-f83403a50a27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_spaceOf_inner_ccbadeb1b04f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_deg_bundle_eq_a4a2fdc96f75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_isLattice_map_db084c5c64a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_image_localLattice_dc65756c069b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_glMap_glOf_02a0381541fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_glOf_one_bbc23ef9500c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_det_glOf_2256b1540a0a

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
include φ
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
theorem _root_.solution (hB : BAt K r) : AAt K V := by
  intro Nm L₁ L₂ g hg hloc
  set gB : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) :=
    fun v ↦ glOf v ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v))) with hgB
  have hfin : {v | gB v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    have : (localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) = 1 :=
      LinearEquiv.ext fun x ↦ by simp [h1]
    simp only [hgB, this, glOf_one]
  have hloc' : ∀ v, localLattice v (L₂.carrier.map (intEquiv φ).toLinearMap) =
      (localLattice v (L₁.carrier.map (intEquiv φ).toLinearMap)).map (glMap v (gB v)) := by
    intro v
    apply SetLike.coe_injective
    rw [Submodule.map_coe, ← image_localLattice, ← image_localLattice, hloc v, ← Set.image_comp,
      ← Set.image_comp]
    congr 1
    funext x
    simp only [hgB, Function.comp_apply, glMap_glOf, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have hM₁ := isLattice_map φ L₁
  have hM₂ := isLattice_map φ L₂
  have key := hB (spaceOf φ Nm) _ _ hM₁ hM₂ gB hfin hloc'
  rw [deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₂ hM₂.1,
    deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₁ hM₁.1, key]
  have hdet : ∀ v, (gB v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det =
      LinearMap.det (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
        (v.adicCompletion K ⊗[K] V)) := by
    intro v
    simp only [hgB]
    rw [det_glOf]
    have : ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) :
        (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) =
        (localEquiv φ v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm : _ →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj]
  simp only [hdet]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
