-- Prove2me | solution 1 for StrategicObfuscation.payoff_formulas
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:13:14.412283+00:00
-- url     : https://prove2.me/submissions/9bda9878-1404-4e97-9a91-f963a924f978

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_sponsorPayoff

open Set

open StrategicObfuscation in
theorem solution {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    (0 < α → α < 1 →
      Q * V = c ∧ (1 - π σ 0) * p * (V - c) = (1 - p) * (1 - π σ e) * c) ∧
    (α < 1 → sponsorPayoff π V c p σ α e = p * (V - c) * π σ 0) ∧
    (α = 1 → sponsorPayoff π V c p σ α e = p * V - c + (1 - p) * π σ e * c) := by
  have part1 : 0 < α → α < 1 →
      Q * V = c ∧ (1 - π σ 0) * p * (V - c) = (1 - p) * (1 - π σ e) * c := by
    intro h0 h1
    have o0 := heq.optimal 0 ⟨le_refl _, zero_le_one⟩
    have o1 := heq.optimal 1 ⟨zero_le_one, le_refl _⟩
    have hx1 : 0 ≤ Q * V - c := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg h0 hneg
      linarith
    have hx2 : Q * V - c ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      have := mul_pos (sub_pos.mpr h1) hpos
      linarith
    have hQV : Q * V = c := by linarith
    refine ⟨hQV, ?_⟩
    have hb := heq.bayes
    linear_combination (-V) * hb + ((1 - π σ 0) * p + (1 - π σ e) * (1 - p)) * hQV
  refine ⟨part1, ?_, ?_⟩
  · intro h1
    unfold sponsorPayoff
    rcases (heq.mem_alpha.1).lt_or_eq with h0 | h0
    · have := (part1 h0 h1).2
      linear_combination α * this
    · rw [← h0]; ring
  · intro h
    subst h
    unfold sponsorPayoff
    ring
