-- Prove2me | solution 1 for WorkbookCorrected.plus_29166
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:45:47.065474+00:00
-- url     : https://prove2.me/submissions/dbb5ec7f-d2c8-4ea7-a332-0fd4f02b6a2f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
private lemma step (x : ℝ) (hl : 1 ≤ x) (hu : x ≤ 3/2) :
    1 ≤ (x^2-x+1)/x ∧ (x^2-x+1)/x ≤ 3/2 ∧
    (x^2-x+1)/x-1 ≤ (1/3)*(x-1) := by
  have hx : 0 < x := by linarith
  have he : (x^2-x+1)/x*x = x^2-x+1 := div_mul_cancel₀ _ (ne_of_gt hx)
  have hp := mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ 3/2-x by linarith)
  have hlo : 1 ≤ (x^2-x+1)/x := (le_div_iff₀ hx).mpr (by nlinarith [sq_nonneg (x-1)])
  have hcon : (x^2-x+1)/x-1 ≤ (1/3)*(x-1) := by
    apply (mul_le_mul_iff_left₀ hx).mp
    nlinarith only [he,hp]
  exact ⟨hlo,by linarith,hcon⟩

theorem solution (a : ℕ → ℝ) (h1 : a 1 = 3/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2-a n+1)/a n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε := by
  have hb : ∀ n : ℕ, 1 ≤ a (n+1) ∧ a (n+1) ≤ 3/2 ∧ a (n+1)-1 ≤ (1/3:ℝ)^n := by
    intro n
    induction n with
    | zero => rw [h1]; norm_num
    | succ n ih =>
      have hh := step (a (n+1)) ih.1 ih.2.1
      rw [show n+1+1=(n+1)+1 by omega, h (n+1) (by omega)]
      refine ⟨hh.1,hh.2.1,?_⟩
      calc
        (a (n+1)^2-a (n+1)+1)/a (n+1)-1 ≤ (1/3)*(a (n+1)-1) := hh.2.2
        _ ≤ (1/3)*(1/3:ℝ)^n := mul_le_mul_of_nonneg_left ih.2.2 (by norm_num)
        _ = (1/3:ℝ)^(n+1) := by rw [pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => (1/3:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hp) ε hε
  refine ⟨K+1,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hh := hK m (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr (hb m).1)]
  exact lt_of_le_of_lt (hb m).2.2 hh
example : (∀ (a : ℕ → ℝ) (h1 : a 1 = 3/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2-a n+1)/a n),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε) := @solution
#print axioms solution
