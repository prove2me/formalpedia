-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.cobham_priority_waits
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:04:58.988977+00:00
-- url     : https://prove2.me/submissions/45be4410-dc61-4f10-9158-b9c4c468742b

import Mathlib

namespace CobhamPV

lemma partial_sum (r : ℕ) (ρ σ W : ℕ → ℝ) (E : ℝ)
    (hσ : ∀ k, σ k = ∑ i ∈ Finset.Icc 1 k, ρ i) (hlt : ∀ i ≤ r, σ i < 1)
    (hW : ∀ i ∈ Finset.Icc 1 r, W i = E / ((1 - σ (i - 1)) * (1 - σ i))) :
    ∀ i ≤ r, ∑ k ∈ Finset.Icc 1 i, ρ k * W k + E = E / (1 - σ i) := by
  intro i
  induction i with
  | zero => intro _; simp [hσ]
  | succ n ih =>
    intro hn
    have hs : σ (n + 1) = σ n + ρ (n + 1) := by
      rw [hσ, hσ, Finset.sum_Icc_succ_top (by omega)]
    have h1 : 1 - σ n ≠ 0 := by linarith [hlt n (by omega)]
    have h2 : 1 - σ (n + 1) ≠ 0 := by linarith [hlt (n + 1) hn]
    rw [Finset.sum_Icc_succ_top (by omega), add_right_comm, ih (by omega),
      hW (n + 1) (Finset.mem_Icc.2 ⟨by omega, hn⟩)]
    simp only [Nat.add_sub_cancel]
    rw [hs] at h2 ⊢
    field_simp
    ring

lemma main_iff (r : ℕ) (ρ σ W : ℕ → ℝ) (E : ℝ)
    (hσ : ∀ k, σ k = ∑ i ∈ Finset.Icc 1 k, ρ i) (hlt : ∀ i ≤ r, σ i < 1) :
    (∀ i ∈ Finset.Icc 1 r, W i = (∑ k ∈ Finset.Icc 1 i, ρ k * W k + E) / (1 - σ (i - 1))) ↔
      (∀ i ∈ Finset.Icc 1 r, W i = E / ((1 - σ (i - 1)) * (1 - σ i))) := by
  constructor
  · intro hE
    have key : ∀ n ≤ r, ∀ i ∈ Finset.Icc 1 n, W i = E / ((1 - σ (i - 1)) * (1 - σ i)) := by
      intro n
      induction n with
      | zero => intro _ i hi; obtain ⟨_, _⟩ := Finset.mem_Icc.1 hi; omega
      | succ n ih =>
        intro hn i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
        rcases Nat.lt_or_ge i (n + 1) with h | h
        · exact ih (by omega) i (Finset.mem_Icc.2 ⟨hi1, by omega⟩)
        · have hi' : i = n + 1 := by omega
          subst hi'
          have hps := partial_sum n ρ σ W E hσ (fun j hj => hlt j (by omega)) (ih (by omega)) n le_rfl
          have heq := hE (n + 1) (Finset.mem_Icc.2 ⟨by omega, hn⟩)
          have hs : σ (n + 1) = σ n + ρ (n + 1) := by
            rw [hσ, hσ, Finset.sum_Icc_succ_top (by omega)]
          have h1 : 1 - σ n ≠ 0 := by linarith [hlt n (by omega)]
          have h2 : 1 - σ (n + 1) ≠ 0 := by linarith [hlt (n + 1) hn]
          rw [Finset.sum_Icc_succ_top (by omega), add_right_comm, hps] at heq
          simp only [Nat.add_sub_cancel] at heq ⊢
          rw [eq_div_iff h1] at heq
          rw [eq_div_iff (mul_ne_zero h1 h2), hs]
          have ha : E / (1 - σ n) * (1 - σ n) = E := div_mul_cancel₀ E h1
          linear_combination (1 - σ n) * heq + ha
    exact key r le_rfl
  · intro hW i hi
    have hps := partial_sum r ρ σ W E hσ hlt hW i (Finset.mem_Icc.1 hi).2
    rw [hps, hW i hi, div_div, mul_comm]

end CobhamPV

theorem solution (r : ℕ) (lamk muk : ℕ → ℝ)
    (hlam : ∀ k ∈ Finset.Icc 1 r, 0 < lamk k) (hmu : ∀ k ∈ Finset.Icc 1 r, 0 < muk k)
    (ρ σ : ℕ → ℝ) (hρ : ∀ k, ρ k = lamk k / muk k) (hσ : ∀ k, σ k = ∑ i ∈ Finset.Icc 1 k, ρ i)
    (hσr : σ r < 1) :
    (∀ (ES0 : ℝ) (W : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 r, W i = (∑ k ∈ Finset.Icc 1 i, ρ k * W k + ES0) / (1 - σ (i - 1))) ↔
        (∀ i ∈ Finset.Icc 1 r, W i = ES0 / ((1 - σ (i - 1)) * (1 - σ i)))) ∧
    (∀ W : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 r, W i =
          (∑ k ∈ Finset.Icc 1 i, ρ k * W k + ∑ k ∈ Finset.Icc 1 r, ρ k / muk k) / (1 - σ (i - 1))) ↔
        (∀ i ∈ Finset.Icc 1 r,
          W i = (∑ k ∈ Finset.Icc 1 r, ρ k / muk k) / ((1 - σ (i - 1)) * (1 - σ i)))) := by
  have hlt : ∀ i ≤ r, σ i < 1 := by
    intro i hi
    have : σ i ≤ σ r := by
      rw [hσ, hσ]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hi)
      intro k hk _
      rw [hρ]
      exact (div_pos (hlam k hk) (hmu k hk)).le
    linarith
  have main : ∀ (ES0 : ℝ) (W : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 r, W i = (∑ k ∈ Finset.Icc 1 i, ρ k * W k + ES0) / (1 - σ (i - 1))) ↔
        (∀ i ∈ Finset.Icc 1 r, W i = ES0 / ((1 - σ (i - 1)) * (1 - σ i))) :=
    fun E W => CobhamPV.main_iff r ρ σ W E hσ hlt
  exact ⟨main, fun W => main _ W⟩
