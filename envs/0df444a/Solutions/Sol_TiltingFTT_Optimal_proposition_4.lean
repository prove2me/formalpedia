-- Prove2me | solution 1 for TiltingFTT.Optimal.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:52:32.321363+00:00
-- url     : https://prove2.me/submissions/a8b0d984-63f9-4501-89a8-c54a2c84e2a5

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model
import Theorems.Thm_TiltingFTT_Optimal_proposition_2
import Theorems.Thm_TiltingFTT_Optimal_proposition_3

open TiltingFTT.Optimal

theorem solution (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    (Cond15 P τ → P.δI * P.FbL < (1 + τ) * P.δU * Fbar P →
      (∃ TH TL, IsSeparatingEq P τ TH TL) ∧ ¬ ∃ TP, IsPoolingEq P τ TP) ∧
    (Coexist P τ →
      (∃ TH TL, IsSeparatingEq P τ TH TL) ∧ ∃ TP, IsPoolingEq P τ TP) := by
  have P2 := (proposition_2 P τ hS hτ).1
  have P3 := (proposition_3 P τ hS hτ).1
  refine ⟨fun h15 hlt => ⟨P2.2 h15, fun hp => ?_⟩, fun hc => ⟨P2.2 ?_, P3.2 ⟨hc.2.1, hc.1.le⟩⟩⟩
  · have := (P3.1 hp).2
    linarith
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    have hδI : 0 < P.δI := by linarith
    have hFbL : P.FbL < Fbar P := by
      unfold Fbar; nlinarith [mul_pos h11 (sub_pos.2 h8)]
    have hFb : 0 < Fbar P := by linarith
    unfold Cond15
    by_contra hk
    rw [not_le] at hk
    have := mul_le_mul_of_nonneg_right hk.le hFb.le
    have := mul_lt_mul_of_pos_left hFbL hδI
    linarith [hc.1]
