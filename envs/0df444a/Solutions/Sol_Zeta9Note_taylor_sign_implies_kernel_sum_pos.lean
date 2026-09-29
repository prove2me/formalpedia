-- Prove2me | solution 1 for Zeta9Note.taylor_sign_implies_kernel_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:24:03.197165+00:00
-- url     : https://prove2.me/submissions/6ab693ce-e537-48f7-a8dd-7be091dc738d

-- Public-mission submission for Zeta9Note.taylor_sign_implies_kernel_sum_pos.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

import Mathlib

theorem solution
    (R u : ℕ → ℝ) (p : Polynomial ℝ) (u₀ : ℝ)
    (hR : ∀ k : ℕ, 0 < R k)
    (hu : ∀ k : ℕ, u₀ ≤ u k)
    (hcoeff : ∀ i : ℕ, 0 ≤ (Polynomial.taylor u₀ p).coeff i)
    (hsummable : Summable (fun k : ℕ => R k * p.eval (u k)))
    (hnonzero : ∃ k : ℕ, 0 < p.eval (u k)) :
    0 < ∑' k : ℕ, R k * p.eval (u k) := by
  have hte : ∀ k : ℕ, p.eval (u k) = (Polynomial.taylor u₀ p).eval (u k - u₀) := by
    intro k
    rw [Polynomial.taylor_eval]
    congr 1
    ring
  have hterm : ∀ k : ℕ, 0 ≤ R k * p.eval (u k) := by
    intro k
    have hsk : 0 ≤ u k - u₀ := sub_nonneg.mpr (hu k)
    have htn : 0 ≤ (Polynomial.taylor u₀ p).eval (u k - u₀) := by
      rw [Polynomial.eval_eq_sum_range]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hcoeff i) (pow_nonneg hsk i)
    rw [hte k]
    exact mul_nonneg (le_of_lt (hR k)) htn
  obtain ⟨k₀, hk₀⟩ := hnonzero
  have hstrict : (fun _ : ℕ => (0 : ℝ)) k₀ < (fun k : ℕ => R k * p.eval (u k)) k₀ :=
    mul_pos (hR k₀) hk₀
  have hlt := Summable.tsum_lt_tsum_of_nonneg
    (f := fun _ : ℕ => (0 : ℝ)) (g := fun k : ℕ => R k * p.eval (u k))
    (fun _ => le_refl 0) hterm hstrict hsummable
  simpa using hlt
