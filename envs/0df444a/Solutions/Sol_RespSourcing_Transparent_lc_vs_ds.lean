-- Prove2me | solution 1 for RespSourcing.Transparent.lc_vs_ds
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:19.856533+00:00
-- url     : https://prove2.me/submissions/ae3e4ae4-41ed-430b-9c2b-f962dcbe0206

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing)
    (hθ : 0 < p.θ) (hαφ : p.α * p.φ < 1) :
    (profit p .DS < profit p .LC ↔ p.r < p.Δ) ∧
    (profit p .LC < profit p .DS ↔ p.Δ < p.r) := by
  have hc : 0 < (1 - p.α * p.φ) * p.θ := mul_pos (by linarith) hθ
  have key : profit p .LC - profit p .DS = ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) := by
    simp only [profit, Params.Δ]; ring
  constructor
  · constructor
    · intro h
      by_contra hn
      have h2 : ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith [not_lt.1 hn])
      linarith
    · intro h
      have : 0 < ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) := mul_pos hc (by linarith)
      linarith
  · constructor
    · intro h
      by_contra hn
      have h2 : 0 ≤ ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) :=
        mul_nonneg hc.le (by linarith [not_lt.1 hn])
      linarith
    · intro h
      have : ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
      linarith
