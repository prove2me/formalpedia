-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.irreducible_has_nonzero_partial
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:54.215063+00:00
-- url     : https://prove2.me/submissions/4cf3f721-7ee8-4b9e-ab76-423b0783ccd0

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h : PlanePoly) (hh : Irreducible h) :
    MvPolynomial.pderiv (0 : Fin 2) h ≠ 0 ∨
    MvPolynomial.pderiv (1 : Fin 2) h ≠ 0 := by
  classical
  by_cases h0 : MvPolynomial.pderiv (0 : Fin 2) h = 0
  · by_cases h1 : MvPolynomial.pderiv (1 : Fin 2) h = 0
    · exfalso
      let p : Polynomial (Polynomial ℝ) := (Polynomial.Bivariate.equivMvPolynomial ℝ).symm h
      have hp : (Polynomial.Bivariate.equivMvPolynomial ℝ) p = h := by
        simp [p]
      have hp1 : Polynomial.derivative p = 0 := by
        have h1' : (MvPolynomial.pderiv (1 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
          simpa [p, hp] using h1
        rw [Polynomial.Bivariate.pderiv_one_equivMvPolynomial] at h1'
        have h1'' :
            (Polynomial.Bivariate.equivMvPolynomial ℝ) (Polynomial.derivative p) =
              (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
          simpa using h1'
        exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h1''
      have hp_nat : p.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hp1
      rcases (Polynomial.natDegree_eq_zero.mp hp_nat) with ⟨q, hq⟩
      have h0' : PolynomialModule.single (Polynomial ℝ) 0 (Polynomial.derivative q) = 0 := by
        have h0'' : Polynomial.derivative'.mapCoeffs p = 0 := by
          have h0''0 : (MvPolynomial.pderiv (0 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
            simpa [p, hp] using h0
          rw [Polynomial.Bivariate.pderiv_zero_equivMvPolynomial] at h0''0
          have h0''1 : PolynomialModule.equivPolynomialSelf
              (Polynomial.derivative'.mapCoeffs p) = 0 := by
            have h0''0' :
                (Polynomial.Bivariate.equivMvPolynomial ℝ)
                    (PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)) =
                  (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
              simpa using h0''0
            exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h0''0'
          have h0''1' :
              PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p) =
                PolynomialModule.equivPolynomialSelf 0 := by
            simpa using h0''1
          exact PolynomialModule.equivPolynomialSelf.injective h0''1'
        rw [← hq] at h0''
        simpa [Polynomial.derivative'_apply] using h0''
      have hqder : Polynomial.derivative q = 0 := by
        have hqder' :=
          congrArg (fun r : PolynomialModule (Polynomial ℝ) (Polynomial ℝ) => r.coeff 0) h0'
        simpa [PolynomialModule.coeff_single] using hqder'
      have hq_nat : q.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hqder
      rcases (Polynomial.natDegree_eq_zero.mp hq_nat) with ⟨r, hr⟩
      have hconst : h = MvPolynomial.C r := by
        rw [← hp, ← hq, ← hr]
        simp
      by_cases hr0 : r = 0
      · subst hr0
        have hz0 := hh.ne_zero
        rw [hconst] at hz0
        simp at hz0
      · have hunitq : IsUnit r := by
          exact isUnit_iff_ne_zero.2 hr0
        have hunit : IsUnit h := by
          rw [hconst]
          exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ) hunitq
        exact hh.not_isUnit hunit
    · exact Or.inr h1
  · exact Or.inl h0
