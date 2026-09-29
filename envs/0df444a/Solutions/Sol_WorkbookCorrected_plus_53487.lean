-- Prove2me | solution 1 for WorkbookCorrected.plus_53487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:20:56.318473+00:00
-- url     : https://prove2.me/submissions/0e62c812-57e7-4fc3-af85-af8115d66836

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=1)
    (h : ∀ n : ℕ, a (n+2)=a (n+1)-(1/4)*a n) :
    ∃ l : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-l| < ε := by
  have hb : ∀ n : ℕ, 0 < a (n+1) ∧ (1/2)*a n ≤ a (n+1) ∧
      a (n+1) ≤ a n ∧ a (n+1) ≤ (3/4:ℝ)^n := by
    intro n
    induction n with
    | zero => rw [h0,h1]; norm_num
    | succ n ih =>
      rw [show n+1+1=n+2 by omega,h n]
      refine ⟨by linarith [ih.1,ih.2.1],by linarith [ih.2.1],by linarith [ih.1,ih.2.2.1],?_⟩
      calc
        a (n+1)-(1/4)*a n ≤ (3/4)*a (n+1) := by linarith [ih.2.2.1]
        _ ≤ (3/4)*(3/4:ℝ)^n := mul_le_mul_of_nonneg_left ih.2.2.2 (by norm_num)
        _ = (3/4:ℝ)^(n+1) := by rw [pow_succ]; ring
  have hp : Tendsto (fun n : ℕ => (3/4:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨0,?_⟩
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hp) ε hε
  refine ⟨K+1,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hh := hK m (by omega)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hh
  rw [sub_zero,abs_of_pos (hb m).1]
  exact lt_of_le_of_lt (hb m).2.2.2 hh
example : (∀ (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=1)
    (h : ∀ n : ℕ, a (n+2)=a (n+1)-(1/4)*a n),
    ∃ l : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-l| < ε) := @solution
#print axioms solution
