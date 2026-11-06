-- Prove2me | solution 1 for SymBoolPCSP.CFixing.sum_conditions_add_closed
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T20:18:13.231901+00:00
-- url     : https://prove2.me/submissions/8d8dede9-80ca-44f9-98e7-50ab9f3dbd26

import Mathlib

namespace SymBoolPCSP.CFixing

/-- The sum conditions (1)–(2) of Lemma 4.9 (bounded by `N`), with `n ≥ 2`, `0 ∈ S₀`,
`1 ∈ S₁`, make both `S₀` and `S₁` closed under adding `2n-2` and adding `3n-4`
(as long as the result is at most `N`). -/
theorem sum_conditions_add_closed (n N : ℕ) (hn : 2 ≤ n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (∀ x ∈ S₀, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₀) ∧
    (∀ x ∈ S₀, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₀) ∧
    (∀ x ∈ S₁, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₁) ∧
    (∀ x ∈ S₁, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₁) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hs1' : ∀ a ∈ S₀, ∀ b : Fin (m + 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁ := hs1
  -- (3): a ∈ S₀ ⇒ a + (m+1) ∈ S₁
  have st3 : ∀ a ∈ S₀, a + (m + 1) ≤ N → a + (m + 1) ∈ S₁ := by
    intro a ha hN
    have := hs1' a ha (fun _ => 1) (fun _ => h1) (by simpa using hN)
    simpa using this
  -- (4): b ∈ S₁ ⇒ b + (m+1) ∈ S₀
  have st4 : ∀ b ∈ S₁, b + (m + 1) ≤ N → b + (m + 1) ∈ S₀ := by
    intro b hb hN
    have hsum : ∑ i, (Fin.cons b (fun _ : Fin (m + 1) => (1 : ℕ)) : Fin (m + 2) → ℕ) i =
        b + (m + 1) := by simp [Fin.sum_cons]
    have := hs0 (Fin.cons b (fun _ => 1)) (fun i => Fin.cases hb (fun _ => h1) i)
      (by rw [hsum]; exact hN)
    rwa [hsum] at this
  -- (5): b ∈ S₁ ⇒ b + m ∈ S₁
  have st5 : ∀ b ∈ S₁, b + m ≤ N → b + m ∈ S₁ := by
    intro b hb hN
    have hsum : ∑ i, (Fin.cons b (fun _ : Fin m => (1 : ℕ)) : Fin (m + 1) → ℕ) i = b + m := by
      simp [Fin.sum_cons]
    have := hs1' 0 h0 (Fin.cons b (fun _ => 1)) (fun i => Fin.cases hb (fun _ => h1) i)
      (by rw [hsum]; omega)
    rwa [hsum, zero_add] at this
  have e2 : 2 * (m + 2) - 2 = (m + 1) + (m + 1) := by omega
  have e3 : 3 * (m + 2) - 4 = (m + 1) + m + (m + 1) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hN; rw [e2] at hN ⊢; rw [← add_assoc]
    exact st4 _ (st3 x hx (by omega)) (by omega)
  · intro x hx hN; rw [e3] at hN ⊢
    have : x + (m + 1 + m + (m + 1)) = x + (m + 1) + m + (m + 1) := by ring
    rw [this]
    exact st4 _ (st5 _ (st3 x hx (by omega)) (by omega)) (by omega)
  · intro x hx hN; rw [e2] at hN ⊢; rw [← add_assoc]
    exact st3 _ (st4 x hx (by omega)) (by omega)
  · intro x hx hN; rw [e3] at hN ⊢
    have : x + (m + 1 + m + (m + 1)) = x + m + (m + 1) + (m + 1) := by ring
    rw [this]
    exact st3 _ (st4 _ (st5 x hx (by omega)) (by omega)) (by omega)

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (n N : ℕ) (hn : 2 ≤ n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (∀ x ∈ S₀, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₀) ∧
    (∀ x ∈ S₀, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₀) ∧
    (∀ x ∈ S₁, x + (2 * n - 2) ≤ N → x + (2 * n - 2) ∈ S₁) ∧
    (∀ x ∈ S₁, x + (3 * n - 4) ≤ N → x + (3 * n - 4) ∈ S₁) :=
  SymBoolPCSP.CFixing.sum_conditions_add_closed n N hn S₀ S₁ h0 h1 hs0 hs1
