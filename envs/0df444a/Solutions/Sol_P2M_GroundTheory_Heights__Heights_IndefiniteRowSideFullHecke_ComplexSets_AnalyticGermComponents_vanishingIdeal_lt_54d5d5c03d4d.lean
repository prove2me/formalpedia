-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:30.691587+00:00
-- url     : https://prove2.me/submissions/f8c40787-2cef-4099-b2e0-969ba16df339

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_anti_2aaf929d994e

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
theorem _root_.solution {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by
  refine lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_
  have hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w :=
    (mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)
  rw [← heq] at hm
  exact (mem_vanishingIdeal_iff hf).1 hm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
