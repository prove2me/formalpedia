-- Prove2me | solution 1 for PositivityTheory.RL.Up.bdd_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:08:40.840056+00:00
-- url     : https://prove2.me/submissions/4236e588-15f0-4f1d-92d2-2d99e49f6c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
namespace PositivityTheory.RL.Up
theorem _root_.solution {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (h : ℝ → B)
    (hc : ∀ φ : B →L[ℂ] ℂ, Continuous fun t => φ (h t)) : ∃ M, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖h t‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : Set.Icc (-1 : ℝ) 1 => NormedSpace.inclusionInDoubleDual ℂ B (h t))
    fun φ => by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc φ).continuousOn
      exact ⟨C, fun t => hC t t.2⟩
  refine ⟨C, fun t ht => ?_⟩
  have := hC ⟨t, ht⟩
  rwa [show ‖NormedSpace.inclusionInDoubleDual ℂ B (h t)‖ = ‖h t‖ from
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := B)).norm_map (h t)] at this
end PositivityTheory.RL.Up
