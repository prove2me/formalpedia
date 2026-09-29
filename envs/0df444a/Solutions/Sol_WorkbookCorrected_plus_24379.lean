-- Prove2me | solution 1 for WorkbookCorrected.plus_24379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:35:40.464824+00:00
-- url     : https://prove2.me/submissions/630ffd82-cf2a-4987-a8a2-d8d9fc98d6bd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

theorem solution (x : ℕ → ℝ) (h1 : x 1 = 3) (h2 : x 2 = -7)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2) = (x n+x (n+1))/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n - (-11/3)| < ε := by
  have hf : ∀ n : ℕ,
      x (n+1) = -11/3 + 20/3*(-1/2:ℝ)^n ∧
      x (n+2) = -11/3 + 20/3*(-1/2:ℝ)^(n+1) := by
    intro n
    induction n with
    | zero => norm_num [h1,h2]
    | succ n ih =>
      constructor
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using ih.2
      · rw [show n+1+2 = (n+1)+2 by omega, h (n+1) (by omega)]
        rw [show n+1+1 = n+2 by omega, ih.1, ih.2]
        simp only [Nat.succ_eq_add_one, pow_succ]
        ring
  have hp : Tendsto (fun n : ℕ => (-1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have ht : Tendsto (fun n : ℕ => -11/3 + 20/3*(-1/2:ℝ)^n) atTop (𝓝 (-11/3:ℝ)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hp))
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp ht) ε hε
  refine ⟨K+1, ?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1, by omega⟩
  rw [(hf m).1]
  simpa only [Real.dist_eq] using hK m (by omega)
example : (∀ (x : ℕ → ℝ) (h1 : x 1 = 3) (h2 : x 2 = -7)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2) = (x n+x (n+1))/2),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n - (-11/3)| < ε) := @solution
#print axioms solution
