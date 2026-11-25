-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:57.388179+00:00
-- url     : https://prove2.me/submissions/62805ac6-2362-46c3-9a5f-977b1214cfb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
theorem _root_.solution {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by
  constructor
  · rintro ⟨g, hg, hg0⟩
    have he : g =ᶠ[𝓝 w] f := Germ.coe_eq.1 hg
    filter_upwards [hg0, he] with z h1 h2 hz
    rw [← h2]
    exact h1 hz
  · intro h
    exact ⟨f, rfl, h⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
