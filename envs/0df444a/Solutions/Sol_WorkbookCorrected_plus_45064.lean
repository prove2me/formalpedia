-- Prove2me | solution 1 for WorkbookCorrected.plus_45064
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:11:42.370147+00:00
-- url     : https://prove2.me/submissions/b0064ba8-c87a-4691-8c48-87f2be3ebdab

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
private lemma root (t k : ℝ) (ht : 0 < t) (hk : 0 ≤ k)
    (h : t^3=t^2+k*(k+1)*t) : t=k+1 := by
  have he : t*(t-(k+1))*(t+k)=0 := by nlinarith only [h]
  have hp : t+k ≠ 0 := ne_of_gt (by linarith)
  have hh := (mul_eq_zero.mp he).resolve_right hp
  have hf := (mul_eq_zero.mp hh).resolve_left (ne_of_gt ht)
  linarith only [hf]

theorem solution (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ Finset.range n, (a (i+1))^3)=(∑ i ∈ Finset.range n, a (i+1))^2) :
    ∀ n : ℕ, 1 ≤ n → a n=(n:ℝ) := by
  have hall : ∀ n : ℕ, (∑ i ∈ Finset.range n, (a (i+1))^3)=(∑ i ∈ Finset.range n, a (i+1))^2 := by
    intro n
    by_cases hz : n=0
    · subst n; simp
    · exact h n (by omega)
  have next : ∀ n : ℕ, (∑ i ∈ Finset.range n, a (i+1))=(n:ℝ)*((n:ℝ)+1)/2 → a (n+1)=(n:ℝ)+1 := by
    intro n hs
    have hsmall := hall n
    have hbig := hall (n+1)
    rw [Finset.sum_range_succ,Finset.sum_range_succ] at hbig
    rw [hs] at hsmall hbig
    apply root _ _ (ha (n+1) (by omega)) (Nat.cast_nonneg n)
    nlinarith only [hsmall,hbig]
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, a (i+1))=(n:ℝ)*((n:ℝ)+1)/2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,next n ih]
      push_cast
      ring
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  simpa using next m (hsum m)
example : (∀ (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ Finset.range n, (a (i+1))^3)=(∑ i ∈ Finset.range n, a (i+1))^2),
    ∀ n : ℕ, 1 ≤ n → a n=(n:ℝ)) := @solution
#print axioms solution
