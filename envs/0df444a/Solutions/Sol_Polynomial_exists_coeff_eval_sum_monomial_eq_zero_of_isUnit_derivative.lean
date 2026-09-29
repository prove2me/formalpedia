-- Prove2me | solution 1 for Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a0f7c2c2-28ef-5bd4-a11b-4ea321ca6be5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
set_option autoImplicit false

namespace NewtonJet

open Polynomial

variable {A : Type*} [CommRing A]

theorem ringHom_eval {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (p : R[X]) (x : R) :
    g (p.eval x) = (p.map g).eval (g x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem coeff_zero_eval_eq (H : Polynomial (Polynomial A)) (W W' : Polynomial A) (h : W.coeff 0 = W'.coeff 0) :
    (H.eval W).coeff 0 = (H.eval W').coeff 0 := by
  rw [← Polynomial.constantCoeff_apply, ← Polynomial.constantCoeff_apply, ringHom_eval, ringHom_eval,
    Polynomial.constantCoeff_apply, Polynomial.constantCoeff_apply W', h]

theorem eval_add_eq (H : Polynomial (Polynomial A)) (W y : Polynomial A) :
    ∃ Q : Polynomial A, H.eval (W + y) = H.eval W + H.derivative.eval W * y + y ^ 2 * Q := by
  set G := taylor W H with hG
  refine ⟨(G.divX.divX).eval y, ?_⟩
  have hexp : G = C (G.coeff 0) + C (G.coeff 1) * X + X ^ 2 * G.divX.divX := by
    have h1 := divX_mul_X_add G
    have h2 := divX_mul_X_add G.divX
    rw [coeff_divX, zero_add] at h2
    calc G = G.divX * X + C (G.coeff 0) := h1.symm
      _ = (G.divX.divX * X + C (G.coeff 1)) * X + C (G.coeff 0) := by rw [h2]
      _ = C (G.coeff 0) + C (G.coeff 1) * X + X ^ 2 * G.divX.divX := by ring
  have hev : H.eval (W + y) = G.eval y := by
    rw [hG, taylor_eval, add_comm y W]
  rw [hev]
  conv_lhs => rw [hexp]
  rw [hG, taylor_coeff_zero, taylor_coeff_one]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]

theorem coeff_eval_add_C_mul_X_pow (H : Polynomial (Polynomial A)) (W : Polynomial A) (c : A) (n : ℕ)
    (hn : 0 < n) (r : ℕ) (hr : r ≤ n) :
    (H.eval (W + C c * X ^ n)).coeff r =
      (H.eval W).coeff r + (if r = n then (H.derivative.eval W).coeff 0 * c else 0) := by
  obtain ⟨Q, hQ⟩ := eval_add_eq H W (C c * X ^ n)
  rw [hQ, coeff_add, coeff_add]
  have h2 : ((C c * X ^ n) ^ 2 * Q).coeff r = 0 := by
    rw [show (C c * X ^ n) ^ 2 * Q = X ^ (2 * n) * (C (c ^ 2) * Q) by rw [C_pow]; ring, coeff_X_pow_mul']
    rw [if_neg (by omega)]
  have h1 : (H.derivative.eval W * (C c * X ^ n)).coeff r =
      if r = n then (H.derivative.eval W).coeff 0 * c else 0 := by
    rw [show H.derivative.eval W * (C c * X ^ n) = X ^ n * (H.derivative.eval W * C c) by ring, coeff_X_pow_mul']
    by_cases hrn : r = n
    · subst hrn
      simp
    · rw [if_neg (by omega), if_neg hrn]
  rw [h2, add_zero, h1]

theorem exists_jet (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (C w₀)).coeff 0 = 0) (hder : IsUnit ((F.derivative.eval (C w₀)).coeff 0)) (m : ℕ) :
    ∃ W : Polynomial A, W.coeff 0 = w₀ ∧ W.natDegree ≤ m ∧ ∀ r, r ≤ m → (F.eval W).coeff r = 0 := by
  induction m with
  | zero =>
    refine ⟨C w₀, coeff_C_zero, (natDegree_C w₀).le, fun r hr => ?_⟩
    obtain rfl : r = 0 := Nat.le_zero.mp hr
    exact h0
  | succ m ih =>
    obtain ⟨W, hW0, hWdeg, hWr⟩ := ih
    obtain ⟨d, hd⟩ := hder
    have hdW : (F.derivative.eval W).coeff 0 = (F.derivative.eval (C w₀)).coeff 0 :=
      coeff_zero_eval_eq _ _ _ (by rw [hW0, coeff_C_zero])
    refine ⟨W + C (-((F.eval W).coeff (m + 1) * ↑d⁻¹)) * X ^ (m + 1), ?_, ?_, fun r hr => ?_⟩
    · rw [coeff_add, coeff_C_mul_X_pow, if_neg (by omega), add_zero, hW0]
    · refine (natDegree_add_le _ _).trans (max_le (hWdeg.trans (Nat.le_succ m)) ?_)
      exact natDegree_C_mul_X_pow_le _ _
    · rw [coeff_eval_add_C_mul_X_pow F W _ (m + 1) (Nat.succ_pos m) r hr]
      by_cases hrm : r = m + 1
      · subst hrm
        rw [if_pos rfl, hdW, ← hd, mul_neg, mul_left_comm, Units.mul_inv, mul_one, add_neg_cancel]
      · rw [if_neg hrm, add_zero]
        exact hWr r (by omega)

theorem exists_jet_vec (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (C w₀)).coeff 0 = 0) (hder : IsUnit ((F.derivative.eval (C w₀)).coeff 0)) (m : ℕ) :
    ∃ w : Fin (m + 1) → A, w 0 = w₀ ∧
      ∀ r : Fin (m + 1), (F.eval (∑ r' : Fin (m + 1), monomial (r' : ℕ) (w r'))).coeff r = 0 := by
  obtain ⟨W, hW0, hWdeg, hWr⟩ := exists_jet F w₀ h0 hder m
  refine ⟨fun r => W.coeff r, hW0, fun r => ?_⟩
  have hW : (∑ r' : Fin (m + 1), monomial (r' : ℕ) (W.coeff r')) = W := by
    conv_rhs => rw [W.as_sum_range' (m + 1) (Nat.lt_succ_of_le hWdeg)]
    rw [Finset.sum_range (fun i => monomial i (W.coeff i))]
  rw [hW]
  exact hWr r (Nat.le_of_lt_succ r.2)

end NewtonJet

theorem solution
    {A : Type*} [CommRing A] (F : Polynomial (Polynomial A)) (w₀ : A)
    (h0 : (F.eval (Polynomial.C w₀)).coeff 0 = 0)
    (hder : IsUnit ((F.derivative.eval (Polynomial.C w₀)).coeff 0)) (m : ℕ) :
    ∃ w : Fin (m + 1) → A, w 0 = w₀ ∧
      ∀ r : Fin (m + 1), (F.eval (∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w r'))).coeff r = 0 :=
  NewtonJet.exists_jet_vec F w₀ h0 hder m

end S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative
end P2MW
export P2MW.S_Polynomial_exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative (solution)
