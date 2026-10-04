-- Prove2me | solution 1 for ZetaNine.five_sample_sign_forces_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T03:26:09.434782+00:00
-- url     : https://prove2.me/submissions/ba0750b0-bacb-4ab0-b862-940210a393da

import Mathlib
import Theorems.Thm_ZetaNine_quadrature_exact_of_moments

theorem solution
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by
  have hexp : L p = ∑ j : Fin 5, w j * p.eval (y j) :=
    ZetaNine.quadrature_exact_of_moments L y w hmom p hpdeg
  intro hLp
  have hsumzero : ∑ j : Fin 5, w j * p.eval (y j) = 0 := by
    rw [← hexp, hLp]
  have hroot : ∀ j : Fin 5, p.eval (y j) = 0 := by
    intro j
    have hterm : w j * p.eval (y j) = 0 := by
      rcases hsign with hsign | hsign
      · exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (le_of_lt (hw i)) (hsign i))).mp hsumzero j (Finset.mem_univ j)
      · have hnegsum : ∑ i : Fin 5, -(w i * p.eval (y i)) = 0 := by
          rw [Finset.sum_neg_distrib, hsumzero, neg_zero]
        have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 0 ≤ -(w i * p.eval (y i)) :=
          fun i _ => neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hw i)) (hsign i))
        have hzi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnegsum j (Finset.mem_univ j)
        exact neg_eq_zero.mp hzi
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hw j))
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hy hroot
    (by simpa using Nat.lt_succ_of_le hpdeg))
