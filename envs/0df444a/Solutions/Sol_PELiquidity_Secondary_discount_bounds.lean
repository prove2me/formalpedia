-- Prove2me | solution 1 for PELiquidity.Secondary.discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:40:45.519602+00:00
-- url     : https://prove2.me/submissions/337e7e96-619a-4839-83d9-585cb248272f

import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

open PELiquidity.Secondary in
theorem solution (P : PELiquidity.Primary.Params) (muH : ℝ) (E : AllocationSec)
    (hEq : IsEquilibriumSec P muH E) (hTrade : 0 < E.sL) :
    1 - P.δH ≤ discount E ∧ discount E ≤ 1 - P.δL := by
  obtain ⟨hPL, hRL, -, -, -, -, -, -, -, -, -, -, -, -, h3, -, -, h6, hd⟩ := hEq
  have hlo : P.δL * E.RL ≤ E.PL := by
    by_contra h
    push Not at h
    have := h3 h
    linarith
  have hhi : E.PL ≤ P.δH * E.RL := by
    by_contra h
    push Not at h
    have := h6 h
    linarith
  unfold discount
  constructor
  · have : E.PL / E.RL ≤ P.δH := (div_le_iff₀ hRL).2 hhi
    linarith
  · have : P.δL ≤ E.PL / E.RL := (le_div_iff₀ hRL).2 hlo
    linarith
