-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_empiricalEntropyError_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/70d6abf0-8831-4dba-b724-0a0d957d410b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_entropySlack_pos
import Theorems.Thm_TwoDegenerateGraphs_empiricalEntropyError_tendsto_zero

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → empiricalEntropyError L < entropySlack := by
  have heventually :
      ∀ᶠ L : ℕ in Filter.atTop,
        empiricalEntropyError L < entropySlack :=
    (tendsto_order.1 empiricalEntropyError_tendsto_zero).2
      entropySlack entropySlack_pos
  obtain ⟨L₀, hL₀⟩ := (Filter.eventually_atTop.1 heventually)
  refine ⟨max 4 L₀, le_max_left _ _, ?_⟩
  intro L hL
  exact hL₀ L ((le_max_right 4 L₀).trans hL)
end TwoDegenerateGraphs
