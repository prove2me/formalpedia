-- Prove2me | solution 1 for TeamDelegation.Optimal.ordering_75_77
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:42:21.884283+00:00
-- url     : https://prove2.me/submissions/63dd069e-9190-400e-99eb-0a61421147fa

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model
import Theorems.Thm_TeamDelegation_Optimal_threshold_order

open TeamDelegation.Optimal

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) :
    DeltaTilde1 P < DeltaStarSum P ∧
      DeltaStarSum P < DeltaTilde2 P ∧
      DeltaStarSum P < DeltaTilde3 P ∧
      0 < DeltaStarSum P ∧
      DeltaStarSum P < DeltaCritA P + DeltaMaxB P := by
  obtain ⟨_, _, _, hHC, _⟩ := threshold_order P hS hA1
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨h01, h12, hq01, hq12, hqp0, hqp1, hqp2, hc1, hc2, hc3, hc4⟩ := hA1
  have hpmdef : punishmentMean P = P.r * P.p0 + (1 - P.r) * P.q0 := rfl
  have hu : 0 < P.δ * (1 - P.r) := mul_pos hδ0 (by linarith)
  have h1r : 0 < 1 - P.r := by linarith
  have hb : 0 < (1 - P.δ) * (P.p1 - P.p0) := mul_pos (by linarith) (by linarith)
  have hDc : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 := by
    have : P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 =
        (P.p2 - P.p1) + P.δ * (P.p1 - P.p0) := by ring
    rw [this]; have := mul_pos hδ0 (sub_pos.2 h01); linarith
  have hDd : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P := by
    have : P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P =
        (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) + P.δ * (1 - P.r) * (P.p0 - P.q0) := by
      rw [hpmdef]; ring
    rw [this]; have := mul_pos hu (sub_pos.2 hqp0); linarith
  have hStar0 : 0 < DeltaStarSum P := by
    unfold DeltaStarSum
    exact div_pos (mul_pos (by linarith) (by linarith)) hDc
  refine ⟨?_, ?_, ?_, hStar0, ?_⟩
  · -- (75)
    unfold DeltaTilde1 DeltaStarSum
    have hden : 0 < (P.p2 - P.p0) * P.δ * (1 - P.r) := by
      rw [mul_assoc]; exact mul_pos (by linarith) hu
    rw [div_lt_div_iff₀ hden hDc]
    have key : 2 * P.e * (P.p0 - P.q0) * ((P.p2 - P.p0) * P.δ * (1 - P.r)) -
        2 * P.e * (P.p0 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) *
          (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) =
        2 * P.e * ((1 - P.δ) * (P.p1 - P.p0)) *
          (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) := by
      rw [hpmdef]; ring
    have := mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * P.e) hb) hDd
    linarith
  · -- (76)
    unfold DeltaTilde2 DeltaStarSum
    have hden2 : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
        (P.p2 - P.q2) * P.δ * (1 - P.r) := by
      have e2 : P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
          (P.p2 - P.q2) * P.δ * (1 - P.r) = (1 - P.δ) * (P.p2 - P.p1) +
          P.δ * P.r * (P.p2 - P.p0) + P.δ * (1 - P.r) * (P.q2 - P.q0) := by
        rw [hpmdef]; ring
      rw [e2]
      have a1 := mul_pos (sub_pos.2 hδ1) (sub_pos.2 h12)
      have a2 := mul_nonneg (mul_nonneg hδ0.le hr0) (sub_pos.2 (lt_trans h01 h12)).le
      have a3 := mul_pos hu (sub_pos.2 (lt_trans hq01 hq12))
      linarith
    rw [div_lt_div_iff₀ hDc hden2]
    have key : (P.p2 - P.q2) * (2 * P.e) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) -
        2 * P.e * (P.p0 - P.q0) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
          (P.p2 - P.q2) * P.δ * (1 - P.r)) =
        2 * P.e * ((P.p2 - P.p0) - (P.q2 - P.q0)) *
          (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) := by
      rw [hpmdef]; ring
    have := mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * P.e)
      (by linarith : (0:ℝ) < (P.p2 - P.p0) - (P.q2 - P.q0))) hDd
    linarith
  · -- (77)
    unfold DeltaTilde3 DeltaStarSum
    have hden3 : 0 < P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 -
        P.δ * P.r * P.p0 := by
      have e3 : P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 - P.δ * P.r * P.p0 =
          (1 - P.δ) * (P.p2 - P.p1) + P.δ * P.r * (P.p2 - P.p0) := by ring
      rw [e3]
      have a1 := mul_pos (sub_pos.2 hδ1) (sub_pos.2 h12)
      have a2 := mul_nonneg (mul_nonneg hδ0.le hr0) (sub_pos.2 (lt_trans h01 h12)).le
      linarith
    rw [div_lt_div_iff₀ hDc hden3]
    have key : 2 * P.e * ((1 - P.δ) * P.p1 + P.δ * punishmentMean P - P.q0) *
          (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) -
        2 * P.e * (P.p0 - P.q0) * (P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 -
          P.δ * P.r * P.p0) =
        2 * P.e * ((1 - P.δ) * (P.p1 - P.p0)) *
          (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) := by
      rw [hpmdef]; ring
    have := mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * P.e) hb) hDd
    linarith
  · -- Δ* = 2 Δ̂_A < Δ_A^crit + Δ_B^max, using Δ̂_A < Δ_A^crit and Δ̂_A < Δ_B^max
    have hStar : DeltaStarSum P = 2 * DeltaHatA P := by
      unfold DeltaStarSum DeltaHatA; ring
    have hHB : DeltaHatA P < DeltaMaxB P := by
      unfold DeltaHatA DeltaMaxB
      have hden : 0 < (1 - P.r) * (P.p2 - P.p1) := mul_pos h1r (by linarith)
      rw [div_lt_div_iff₀ hDc hden]
      have key : P.e * (P.p1 - punishmentMean P) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) -
          P.e * (P.p0 - P.q0) * ((1 - P.r) * (P.p2 - P.p1)) =
          P.e * (P.p1 - P.p0) * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) +
          P.e * (1 - P.r) * (P.p0 - P.q0) * (P.δ * (P.p1 - P.p0)) := by
        rw [hpmdef]; ring
      have a1 := mul_pos (mul_pos he (sub_pos.2 h01)) hDc
      have a2 := mul_pos (mul_pos (mul_pos he h1r) (sub_pos.2 hqp0))
        (mul_pos hδ0 (sub_pos.2 h01))
      linarith
    linarith
