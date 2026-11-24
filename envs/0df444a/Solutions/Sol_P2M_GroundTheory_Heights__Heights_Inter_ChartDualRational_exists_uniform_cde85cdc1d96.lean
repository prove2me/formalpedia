-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:08.951872+00:00
-- url     : https://prove2.me/submissions/758c8f46-9256-4485-b46a-cc55e40104ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter.ChartDualRational
namespace GroundTheory.Heights₂.Heights.Inter.ChartDualRational
theorem _root_.solution {α : Type*} [Fintype α] (P : α → ℕ → Prop) (mono : ∀ a n m, n ≤ m → P a n → P a m)
    (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by
  choose N hN using h
  exact ⟨∑ a, N a, fun a ↦ mono a _ _ (Finset.single_le_sum (by simp) (Finset.mem_univ a)) (hN a)⟩
end GroundTheory.Heights₂.Heights.Inter.ChartDualRational
