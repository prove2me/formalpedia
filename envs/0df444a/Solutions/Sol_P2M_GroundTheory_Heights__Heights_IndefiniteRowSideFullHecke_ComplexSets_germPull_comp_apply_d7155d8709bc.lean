-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:42.813941+00:00
-- url     : https://prove2.me/submissions/7a094ef5-231f-4c55-94dc-3aa785bd5702

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ τ : Type} [Fintype σ] [Fintype τ] {d : ℕ} (w : σ → ℂ)
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)) (φ : holGerms (B (π w))) :
    germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ =
      germPull π (π.analyticAt w) rfl (germPull B (B.analyticAt (π w)) rfl φ) := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 : ((germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑(f ∘ (B.comp π)) := germPull_coe (⇑(B.comp π)) ((B.comp π).analyticAt w) rfl φ f hφ
  have e2 : ((germPull B (B.analyticAt (π w)) rfl φ : holGerms (π w)) : Germ (𝓝 (π w)) ℂ) = ↑(f ∘ B) :=
    germPull_coe _ _ rfl φ f hφ
  exact e1.trans (germPull_coe π (π.analyticAt w) rfl _ (f ∘ B) e2.symm).symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
