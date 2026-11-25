-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_deg_bundle_eq_a4a2fdc96f75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:38.747727+00:00
-- url     : https://prove2.me/submissions/3841f298-2004-42a0-be12-7b26d3cf5aa7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9


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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
theorem _root_.solution (Nm : HermitianNorms K V) (H : HermitianSpace K r)
    (hrel : ∀ (σ : K →+* ℂ) (x y : V), (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)))
    (L : FullLattice K V) (hL : (L.carrier.map (intEquiv φ).toLinearMap).FG) :
    (Nm.bundle L).deg = deg (H.lattice (L.carrier.map (intEquiv φ).toLinearMap) hL) := by
  unfold HermitianBundle.deg deg degOf HermitianBundle.arithDegree
  congr 1
  refine GroundTheory.Heights₂.Heights.LatticeLemmas.arithDegree_congr _ _
    (Submodule.equivMapOfInjective _ (intEquiv φ).injective L.carrier) fun σ x y ↦ ?_
  exact hrel σ (Subtype.val (p := (· ∈ L.carrier)) x) (Subtype.val (p := (· ∈ L.carrier)) y)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
