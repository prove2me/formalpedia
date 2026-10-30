-- Prove2me | solution 1 for RendezvousKn.Sym.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:19:14.365471+00:00
-- url     : https://prove2.me/submissions/c99076ab-b3b4-4174-a685-622595c40257

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model
import Theorems.Thm_RendezvousKn_Sym_lemma_4
import Theorems.Thm_RendezvousKn_Sym_eq_1

open RendezvousKn.Sym

theorem solution (n : ℕ) (hn : 2 ≤ n) (σ : Tactic n → ℝ)
    (hσ : σ ∈ stdSimplex ℝ (Tactic n)) :
    ((n : ℝ) + 1) / 2 + (2 : ℝ) ^ (-36 : ℤ) * n ≤ expWait σ σ := by
  obtain ⟨h0, h1⟩ := hσ
  set c : ℝ := ((n : ℝ) + 1) / 2
  set d : ℝ := (2 : ℝ) ^ (-35 : ℤ) * n
  let s : Tactic n → ℝ := fun τ => if IsPassive τ then 1 else 0
  have hd : 0 ≤ d := by positivity
  -- pointwise bound
  have hW : ∀ a b : Tactic n, c + d * (s a * s b + (1 - s a) * (1 - s b)) ≤ W a b := by
    intro a b
    by_cases ha : IsPassive a <;> by_cases hb : IsPassive b
    · have := lemma_4 n hn a b (by tauto)
      simp only [s, c, d, ha, hb, if_true]; linarith
    · have := eq_1 n hn a b
      simp only [s, c, d, ha, hb, if_true, if_false]; linarith
    · have := eq_1 n hn a b
      simp only [s, c, d, ha, hb, if_true, if_false]; linarith
    · have := lemma_4 n hn a b (by tauto)
      simp only [s, c, d, ha, hb, if_false]; linarith
  have key : ∑ a : Tactic n, ∑ b : Tactic n,
      σ a * σ b * (c + d * (s a * s b + (1 - s a) * (1 - s b))) ≤ expWait σ σ := by
    unfold expWait
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    exact mul_le_mul_of_nonneg_left (hW a b) (mul_nonneg (h0 a) (h0 b))
  set p : ℝ := ∑ a, σ a * s a
  set q : ℝ := ∑ a, σ a * (1 - s a)
  have hpq : p + q = 1 := by
    have e : ∀ a, σ a * s a + σ a * (1 - s a) = σ a := fun a => by ring
    simp only [p, q, ← Finset.sum_add_distrib, e, h1]
  have expand : ∑ a : Tactic n, ∑ b : Tactic n,
      σ a * σ b * (c + d * (s a * s b + (1 - s a) * (1 - s b))) =
      c * ((∑ a, σ a) * (∑ b, σ b)) + d * (p * p + q * q) := by
    have e : ∀ a b, σ a * σ b * (c + d * (s a * s b + (1 - s a) * (1 - s b))) =
        c * (σ a * σ b) + d * (σ a * s a * (σ b * s b)) +
          d * (σ a * (1 - s a) * (σ b * (1 - s b))) := by intros; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, p, q]
    ring
  rw [expand, h1] at key
  have hsq : 1 / 2 ≤ p * p + q * q := by nlinarith [sq_nonneg (p - q)]
  have h36 : (2 : ℝ) ^ (-36 : ℤ) * n = d * (1 / 2) := by
    simp only [d]
    rw [show (-36 : ℤ) = -35 + -1 by norm_num, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num; ring
  rw [h36]; nlinarith [mul_le_mul_of_nonneg_left hsq hd]
