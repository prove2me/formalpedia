-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_bAt_of_aAt_bd1074445082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:34.585903+00:00
-- url     : https://prove2.me/submissions/aa4dc62a-4570-4918-bc8c-0f84e786c985

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_normsOf_inner_798408bc844a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_deg_bundle_eq_a4a2fdc96f75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_deg_lattice_congr_ea34081b52ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_isLattice_map_db084c5c64a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_map_pullLattice_68e6c89e6557
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_image_localLattice_dc65756c069b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_glEquiv_apply_82e6fc68b104
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_glEquiv_one_6b1ebf67b210
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_det_glEquiv_837aa89a78b0

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
theorem _root_.solution (hA : AAt K V) : BAt K r := by
  intro H M₁ M₂ h₁ h₂ g hg hloc
  set gA : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) :=
    fun v ↦ (localEquiv φ v).trans ((glEquiv v (g v)).trans (localEquiv φ v).symm) with hgA
  have hfin : {v | gA v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    refine LinearEquiv.ext fun x ↦ ?_
    simp [hgA, h1, glEquiv_one]
  have hloc' : ∀ v, (Heights.localLattice v (pullLattice φ M₂ h₂).carrier :
      Set (v.adicCompletion K ⊗[K] V)) = gA v '' Heights.localLattice v (pullLattice φ M₁ h₁).carrier := by
    intro v
    apply Set.image_injective.mpr (localEquiv φ v).injective
    rw [image_localLattice, map_pullLattice, hloc v, Set.image_image]
    have : (fun x ↦ localEquiv φ v (gA v x)) = glMap v (g v) ∘ localEquiv φ v := by
      funext x
      simp only [hgA, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Function.comp_apply,
        glEquiv_apply]
    rw [this, Set.image_comp, image_localLattice, map_pullLattice, Submodule.map_coe]
  have key := hA (normsOf φ H) (pullLattice φ M₁ h₁) (pullLattice φ M₂ h₂) gA hfin hloc'
  rw [deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_lattice_congr H (map_pullLattice φ M₂ h₂) _ h₂.1,
    deg_lattice_congr H (map_pullLattice φ M₁ h₁) _ h₁.1] at key
  have hdet : ∀ v, LinearMap.det (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V)) = (g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det := by
    intro v
    have : (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
        ((localEquiv φ v).symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          (glEquiv v (g v) : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm.symm : _ →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj, det_glEquiv]
  simp only [hdet] at key
  exact key
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
