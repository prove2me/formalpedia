-- Prove2me | solution 1 for TeamDelegation.Optimal.cost_comparison
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:01:21.550473+00:00
-- url     : https://prove2.me/submissions/7a96c85f-723c-496f-b20f-543bc9eedecb

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model
open TeamDelegation.Optimal

theorem solution(P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (ΔA ΔB : ℝ)
    (hbranch : ΔA ≤ DeltaCritA P) :
    wdelA P ΔA + wdelB P ΔB < 2 * wcent P ↔
      ΔA + ΔB < DeltaStarSum P := by
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hA1
  have hk : 0 < P.δ * (1 - P.r) := mul_pos hδ0 (by linarith)
  have hD0 : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 := by nlinarith
  have hDp : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P := by
    unfold punishmentMean; nlinarith [mul_pos hk (sub_pos.2 a5)]
  unfold wdelA wdelB wcent DeltaStarSum
  rw [if_pos hbranch]
  have key : (2 * P.e + P.δ * (1 - P.r) * (ΔA + ΔB)) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0)
      - 2 * P.e * (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P)
      = P.δ * (1 - P.r) * ((ΔA + ΔB) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0)
          - 2 * P.e * (P.p0 - P.q0)) := by
    unfold punishmentMean; ring
  set D0 := P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 with hD0d
  set Dp := P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P with hDpd
  have lhs : (P.e + P.δ * (1 - P.r) * ΔA) / Dp + (P.e + P.δ * (1 - P.r) * ΔB) / Dp
      = (2 * P.e + P.δ * (1 - P.r) * (ΔA + ΔB)) / Dp := by ring
  rw [lhs, show 2 * (P.e / D0) = 2 * P.e / D0 by ring, div_lt_div_iff₀ hDp hD0,
    lt_div_iff₀ hD0]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hk.le (sub_nonneg.2 hc)]
  · intro h
    nlinarith [mul_pos hk (sub_pos.2 h)]
