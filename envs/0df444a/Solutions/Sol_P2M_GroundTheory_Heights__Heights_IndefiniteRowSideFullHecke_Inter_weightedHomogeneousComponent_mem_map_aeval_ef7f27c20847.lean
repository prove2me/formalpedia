-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:24.563714+00:00
-- url     : https://prove2.me/submissions/c0a53426-204c-4031-a758-8b8e8992174f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isWeightedHomogeneous_aeval_of_weights_ef9f52113e2f

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
open MvPolynomial
variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution [DecidableEq M] {w : σ → M} {ω : τ → M}
    {e : σ → MvPolynomial τ R} (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v))
    (G : Set (MvPolynomial σ R)) (hG : ∀ f ∈ G, ∃ a, IsWeightedHomogeneous w f a)
    {f : MvPolynomial τ R} (hf : f ∈ Ideal.map (aeval e) (Ideal.span G)) (m : M) :
    weightedHomogeneousComponent ω m f ∈ Ideal.map (aeval e) (Ideal.span G) := by
  let _ := weightedGradedAlgebra R ω
  have hom : (Ideal.map (aeval e) (Ideal.span G)).IsHomogeneous (weightedHomogeneousSubmodule R ω) := by
    rw [Ideal.map_span]
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨f, hfG, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG f hfG
    exact ⟨a, (mem_weightedHomogeneousSubmodule R ω a _).mpr (isWeightedHomogeneous_aeval_of_weights he ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem R ω hom hf m
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
