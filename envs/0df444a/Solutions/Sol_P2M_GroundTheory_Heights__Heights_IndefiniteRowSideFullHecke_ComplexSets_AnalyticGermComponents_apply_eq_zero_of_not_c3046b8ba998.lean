-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_apply_eq_zero_of_not_c3046b8ba998
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:46.390545+00:00
-- url     : https://prove2.me/submissions/0a6ba7f2-3284-467a-9ab8-a1b3bb54b4e7

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
theorem _root_.solution {X : Set (σ → ℂ)} {w : σ → ℂ} {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hfg : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) (hng : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) : f w = 0 := by
  by_contra h0
  apply hng
  have hev : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuousAt.eventually_ne h0
  filter_upwards [hfg, hev] with z h1 h2 hz
  exact (mul_eq_zero.1 (h1 hz)).resolve_left h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
