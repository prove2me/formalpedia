-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:39.949824+00:00
-- url     : https://prove2.me/submissions/af573f0e-01fc-4171-a530-04f7dfff3417

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_zDeg_injective_c39e8e72fba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genericEvaluation_le_c256039eadb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_le_ker_genericEvaluation_940d81026d18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_weightedHomogeneousComponent_of_weights_c46b0d733486
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution [DecidableEq K] (P : Ideal (MRing ι)) (G : Set (MRing ι))
    (hG : ∀ f ∈ G, ∃ a, IsMultiHomog f a) (hPG : P = Ideal.span G) {N1 : ℕ}
    (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    {f : MRing (PBlk ι N1)} (hf : f ∈ RingHom.ker (genMap P fun s j => toFn P (V s j)))
    (b : K ⊕ Unit → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (PBlk ι N1)) b f ∈
      RingHom.ker (genMap P fun s j => toFn P (V s j)) := by
  classical
  rw [genMap_eq_comp] at hf ⊢
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at hf ⊢
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf ⊢
  have hJ := ker_genericEvaluation_le P hf
  have hGw : ∀ g ∈ G, ∃ a, IsWeightedHomogeneous (fun p => zDegInl (NumbersDVR.blockWeight ι p)) g a := by
    intro g hg
    obtain ⟨a, ha⟩ := hG g hg
    refine ⟨zDegInl a, fun d hd => ?_⟩
    rw [NumbersDVR.weight_comp_addMonoidHom, ((Bridge.isMultiHomog_iff g a).mpr ha) hd]
  rw [hPG, rename_eq_aeval] at hJ
  have hc := weightedHomogeneousComponent_mem_map_aeval (ω := genericWeight ι γ) (e := X ∘ Sum.inr)
    (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) G hGw hJ (zDeg b)
  rw [← rename_eq_aeval, ← hPG] at hc
  rw [← aeval_weightedHomogeneousComponent_of_weights
      (fun v => zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) (genericWeight ι γ) (genericSubstitution V)
      (genericSubstitution_isWeightedHomogeneous γ V hV), NumbersDVR.weightedHomogeneousComponent_comp_addMonoidHom zDeg zDeg_injective]
    at hc
  exact map_le_ker_genericEvaluation P hc
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
