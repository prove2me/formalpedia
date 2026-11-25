-- Prove2me | solution 1 for P2M_GlobalTheory_coeff_eval__C_mul_X_25956fd9ea4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:40.524316+00:00
-- url     : https://prove2.me/submissions/67905358-7a7a-4955-81bd-969e69a764d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousComponentsOfConeIntegralEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add, hp, hq]
end GlobalTheory
