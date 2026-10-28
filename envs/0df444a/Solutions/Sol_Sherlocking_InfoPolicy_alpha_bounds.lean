-- Prove2me | solution 1 for Sherlocking.InfoPolicy.alpha_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:54:10.137457+00:00
-- url     : https://prove2.me/submissions/7877491d-e3e8-4b89-841e-4a182fd1b0b3

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

open Sherlocking.InfoPolicy in
theorem solution (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r) (hrK : r < 1 - K) : (0 < thetaS K r ∧ thetaS K r ≤ thetaP K δ r ∧ thetaP K δ r ≤ 1) ∧ ∀ θ ∈ Set.Icc (thetaP K δ r) 1, 0 ≤ alpha K δ θ r ∧ alpha K δ θ r < 1 := by
  have ha : K < 1 - r := by linarith
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < δ := by linarith
  have hapos : 0 < 1 - r := by linarith
  have hS : thetaS K r = K / (1 - r) := by unfold thetaS; rw [if_pos ha]
  have hSle1 : K / (1 - r) < 1 := (div_lt_one hapos).mpr ha
  have hS0 : 0 < K / (1 - r) := div_pos hK0 hapos
  have hP_ge : K / (1 - r) ≤ thetaP K δ r := by
    unfold thetaP
    split_ifs with h
    · rw [div_le_div_iff₀ hapos (by positivity)]
      have := mul_pos (mul_pos hK0 hapos) (sub_pos.mpr hδ1)
      nlinarith
    · linarith
  have hP_le1 : thetaP K δ r ≤ 1 := by
    unfold thetaP
    split_ifs with h
    · exact (div_le_one (by positivity)).mpr h.le
    · exact le_refl _
  refine ⟨⟨by rw [hS]; exact hS0, by rw [hS]; exact hP_ge, hP_le1⟩, ?_⟩
  intro θ hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hθS : K / (1 - r) ≤ θ := hP_ge.trans hθ1
  have hθ0 : 0 < θ := lt_of_lt_of_le hS0 hθS
  have hD : 0 < (1 - r) * θ := mul_pos hapos hθ0
  have hKD : K ≤ (1 - r) * θ := by
    rw [div_le_iff₀ hapos] at hθS; linarith
  have h1 : K / ((1 - r) * θ) ≤ 1 := (div_le_one hD).mpr hKD
  have hDle : (1 - r) * θ ≤ 1 := by nlinarith
  have h2 : 1 - δ < K / ((1 - r) * θ) := by
    rw [lt_div_iff₀ hD]; nlinarith
  unfold alpha
  constructor
  · apply mul_nonneg (by positivity); linarith
  · have e : 1 / δ * (1 - K / ((1 - r) * θ)) = (1 - K / ((1 - r) * θ)) / δ := by ring
    rw [e, div_lt_one hδ0]
    linarith
