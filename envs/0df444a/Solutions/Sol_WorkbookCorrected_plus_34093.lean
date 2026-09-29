-- Prove2me | solution 1 for WorkbookCorrected.plus_34093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:55:08.670585+00:00
-- url     : https://prove2.me/submissions/9eaf2050-625f-4c2a-9eb1-ee025a2fb058

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (x : ℕ → ℝ) (hx : ∀ n : ℕ, 1 ≤ n → 0 < x n)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) ≤ (∑ i ∈ Finset.range n, x (i+1))/(n:ℝ)^2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n| < ε := by
  have hx1 : 0 < x 1 := hx 1 (by omega)
  have hb : ∀ n : ℕ, x (n+1) ≤ x 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hz : n=0
      · subst n; simp
      have hn : 1 ≤ n := by omega
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hp : 0 < (n:ℝ)^2 := by positivity
      have hsum : (∑ i ∈ Finset.range n, x (i+1)) ≤ (n:ℝ)*x 1 := by
        calc
          (∑ i ∈ Finset.range n, x (i+1)) ≤ ∑ i ∈ Finset.range n, x 1 :=
            Finset.sum_le_sum (fun i hi => ih i (Finset.mem_range.mp hi))
          _ = (n:ℝ)*x 1 := by simp
      apply le_trans (h n hn)
      apply (div_le_iff₀ hp).mpr
      have hm := mul_nonneg (show 0 ≤ (n:ℝ)*x 1 by positivity)
        (show 0 ≤ (n:ℝ)-1 by linarith)
      nlinarith only [hsum,hm]
  have hd : ∀ n : ℕ, 1 ≤ n → x (n+1) ≤ x 1/(n:ℝ) := by
    intro n hn
    have hp : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hsum : (∑ i ∈ Finset.range n, x (i+1)) ≤ (n:ℝ)*x 1 := by
      calc
        (∑ i ∈ Finset.range n, x (i+1)) ≤ ∑ i ∈ Finset.range n, x 1 := Finset.sum_le_sum (fun i hi => hb i)
        _ = (n:ℝ)*x 1 := by simp
    calc
      x (n+1) ≤ (∑ i ∈ Finset.range n, x (i+1))/(n:ℝ)^2 := h n hn
      _ ≤ ((n:ℝ)*x 1)/(n:ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = x 1/(n:ℝ) := by field_simp <;> ring
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (x 1/ε+1)
  refine ⟨K+1,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hKm : (K:ℝ) ≤ m := by exact_mod_cast (show K ≤ m by omega)
  have hr : x 1/ε < (m:ℝ) := by linarith
  have hm : (0:ℝ) < m := lt_trans (div_pos hx1 hε) hr
  have hmN : 1 ≤ m := by exact_mod_cast (show (1:ℕ) ≤ m from Nat.one_le_iff_ne_zero.mpr (by intro hz; simp [hz] at hm))
  rw [abs_of_pos (hx (m+1) (by omega))]
  apply lt_of_le_of_lt (hd m hmN)
  apply (div_lt_iff₀ hm).mpr
  have hh := (div_lt_iff₀ hε).mp hr
  nlinarith only [hh]
example : (∀ (x : ℕ → ℝ) (hx : ∀ n : ℕ, 1 ≤ n → 0 < x n)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) ≤ (∑ i ∈ Finset.range n, x (i+1))/(n:ℝ)^2),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n| < ε) := @solution
#print axioms solution
