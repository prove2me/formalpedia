-- Prove2me | solution 1 for WeilConjectures.similar_of_charmatrix_unit_equiv
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T05:32:27.363047+00:00
-- url     : https://prove2.me/submissions/7cdf9283-fe15-4fec-aba7-dd8061be6175

import Mathlib

open Polynomial

namespace SimilarOfCharmatrixAux

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Right evaluation at `B` of `(X - C A) * W`. -/
theorem eval_X_sub_C_mul (A B : Matrix ι ι K) (W : (Matrix ι ι K)[X]) :
    ((X - C A) * W).eval B = W.eval B * B - A * W.eval B := by
  rw [sub_mul, eval_sub, X_mul, eval_mul_X, eval_C_mul]

/-- If `R * B = A * R` and `W(B) = R`, then right evaluation satisfies
`(Q * W)(B) = Q(A) * R`. -/
theorem eval_mul_of_intertwine (A B R : Matrix ι ι K) (hR : R * B = A * R)
    (W : (Matrix ι ι K)[X]) (hW : W.eval B = R) (Q : (Matrix ι ι K)[X]) :
    (Q * W).eval B = Q.eval A * R := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_mul, eval_add, hp, hq, eval_add, add_mul]
  | monomial k M =>
    rw [eval_monomial, ← C_mul_X_pow_eq_monomial, mul_assoc, eval_C_mul, X_pow_mul,
      eval_mul_X_pow, hW, mul_assoc, (SemiconjBy.pow_right hR k).eq]

/-- The classical step: an equivalence `(X - A) W = P (X - B)` with `W` left-invertible
yields an invertible intertwiner `R` with `R B = A R`. -/
theorem intertwiner_of_poly_equiv (A B : Matrix ι ι K) (W P Q : (Matrix ι ι K)[X])
    (h1 : (X - C A) * W = P * (X - C B)) (h2 : Q * W = 1) :
    ∃ R : Matrix ι ι K, Q.eval A * R = 1 ∧ R * B = A * R := by
  have hR : W.eval B * B = A * W.eval B := by
    have := congrArg (Polynomial.eval B) h1
    rw [eval_X_sub_C_mul, eval_mul_X_sub_C] at this
    exact sub_eq_zero.mp this
  refine ⟨W.eval B, ?_, hR⟩
  have := eval_mul_of_intertwine A B _ hR W rfl Q
  rw [h2, eval_one] at this
  exact this.symm

end SimilarOfCharmatrixAux

open SimilarOfCharmatrixAux in
theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι K}
    (h : ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * Matrix.charmatrix A * Q = Matrix.charmatrix B) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' B := by
  classical
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h
  have iP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have iQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
  -- `cA * Q = P⁻¹ * cB`
  have e1 : Matrix.charmatrix A * Q = P⁻¹ * Matrix.charmatrix B := by
    rw [← hPQ]
    simp only [← Matrix.mul_assoc, iP, Matrix.one_mul]
  have h1 : (X - C A) * matPolyEquiv Q = matPolyEquiv P⁻¹ * (X - C B) := by
    rw [← Matrix.matPolyEquiv_charmatrix, ← Matrix.matPolyEquiv_charmatrix, ← map_mul,
      ← map_mul, e1]
  have h2 : matPolyEquiv Q⁻¹ * matPolyEquiv Q = 1 := by
    rw [← map_mul, iQ, map_one]
  obtain ⟨R, hQR, hRB⟩ := intertwiner_of_poly_equiv A B _ _ _ h1 h2
  set S := (matPolyEquiv Q⁻¹).eval A with hS
  have hRS : R * S = 1 := mul_eq_one_comm.mp hQR
  refine ⟨LinearEquiv.ofLinear (Matrix.toLin' S) (Matrix.toLin' R) ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, hQR, Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, hRS, Matrix.toLin'_one]
  · rw [LinearEquiv.conj_apply, LinearEquiv.ofLinear_toLinearMap,
      LinearEquiv.ofLinear_symm_toLinearMap, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    congr 1
    rw [Matrix.mul_assoc, ← hRB, ← Matrix.mul_assoc, hQR, Matrix.one_mul]
