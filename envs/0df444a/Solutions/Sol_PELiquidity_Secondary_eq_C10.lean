-- Prove2me | solution 1 for PELiquidity.Secondary.eq_C10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:40:46.29973+00:00
-- url     : https://prove2.me/submissions/d7a502ef-3ac4-439d-b3a9-a091cdb79eba

import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

open PELiquidity.Secondary in
theorem solution (P : PELiquidity.Primary.Params) (muH : ℝ) (E : AllocationSec)
    (hEq : IsEquilibriumSec P muH E) (hNoH : E.αH = 0)
    (hDlo : 1 - P.δH < discount E)
    (hDhi : discount E < 1 - P.δL) :
    (E.IL - P.A) * E.PL = muH * P.K := by
  obtain ⟨hPL, hRL, -, -, -, -, -, hsum, -, -, -, -, -, h2, -, h4, -, -, hd⟩ := hEq
  unfold discount at hDlo hDhi
  have h1 : E.PL / E.RL < P.δH := by linarith
  have h1' : P.δL < E.PL / E.RL := by linarith
  have hhi : E.PL < P.δH * E.RL := (div_lt_iff₀ hRL).1 h1
  have hlo : P.δL * E.RL < E.PL := (lt_div_iff₀ hRL).1 h1'
  have hs := h2 hlo
  have hdH := h4 hhi
  have hαL : E.αL = 1 := by linarith
  rw [hd, hs, hαL, one_mul] at hdH
  rw [hNoH, zero_mul, sub_zero] at hdH
  rw [hdH]
  field_simp
