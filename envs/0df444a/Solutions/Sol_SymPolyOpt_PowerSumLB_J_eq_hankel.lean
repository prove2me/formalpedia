-- Prove2me | solution 1 for SymPolyOpt.PowerSumLB.J_eq_hankel
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:27:38.777455+00:00
-- url     : https://prove2.me/submissions/4adad988-04e3-4e22-8606-5ec385c5be4a

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

set_option autoImplicit false
open SymPolyOpt.PowerSumLB

theorem solution (n : ℕ) :
    ∀ i j : Fin n, Jmat n i j = MvPolynomial.psum (Fin n) ℝ ((i : ℕ) + (j : ℕ)) := by
  intro i j
  have key : ∀ (a : ℕ) (k : Fin n), MvPolynomial.pderiv k (piInv n (a + 1)) =
      (MvPolynomial.X k : MvPolynomial (Fin n) ℝ) ^ a := by
    intro a k
    have ha : ((a : ℝ) + 1) ≠ 0 := by positivity
    unfold piInv MvPolynomial.psum
    rw [Derivation.map_smul, map_sum]
    have h2 : ∀ l : Fin n, MvPolynomial.pderiv k ((MvPolynomial.X l : MvPolynomial (Fin n) ℝ) ^ (a + 1)) =
        if l = k then ((a + 1 : ℕ) : MvPolynomial (Fin n) ℝ) * (MvPolynomial.X k) ^ a else 0 := by
      intro l
      rw [Derivation.leibniz_pow]
      by_cases hl : l = k
      · subst hl; simp [MvPolynomial.pderiv_X_self]
      · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hl), hl]
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have : (1 / ((a + 1 : ℕ) : ℝ)) * ((a + 1 : ℕ) : ℝ) = 1 := by
      rw [one_div]; exact inv_mul_cancel₀ (by positivity)
    rw [this, one_smul]
  simp only [Jmat, key, MvPolynomial.psum]
  rw [← Finset.sum_congr rfl (fun k _ => (pow_add (MvPolynomial.X k : MvPolynomial (Fin n) ℝ) i j).symm)]
