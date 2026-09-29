-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_specialized_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:51.048198+00:00
-- url     : https://prove2.me/submissions/35078ca6-87f8-423d-8410-dd3d7c074cc2

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (p : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (hx : Specialized0 x p = 0) :
    CoeffLineFactor x ∣ p := by
  let XCoeffEquiv : XCoeff ≃+* Polynomial ℝ :=
    (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans
      (Polynomial.mapEquiv ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv))
  have hEval : ∀ r : XCoeff, Polynomial.eval x (XCoeffEquiv r) = coeffEval x r := by
    intro r
    refine MvPolynomial.induction_on
      (motive := fun r => Polynomial.eval x (XCoeffEquiv r) = coeffEval x r) r ?_ ?_ ?_
    · intro a
      simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
      change MvPolynomial.coeff (0 : Fin 0 →₀ ℕ) (MvPolynomial.C a) = a
      rw [MvPolynomial.coeff_C]
      simp
    · intro r s hr hs
      simp [hr, hs]
    · intro r n hr
      fin_cases n
      rw [map_mul, Polynomial.eval_mul]
      rw [hr]
      simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
  have hX :
      XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) =
        Polynomial.X - Polynomial.C x := by
    rw [map_sub]
    simp [XCoeffEquiv, MvPolynomial.finSuccEquiv_apply]
    change MvPolynomial.coeff (0 : Fin 0 →₀ ℕ) (MvPolynomial.C x) = x
    rw [MvPolynomial.coeff_C]
    simp
  have hcoeff_div :
      ∀ n : ℕ, MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x ∣ (Curry0 p).coeff n := by
    intro n
    have hmap : Polynomial.map (coeffEval x) (Curry0 p) = 0 := by
      simpa [Specialized0] using hx
    have hcoeff0 : coeffEval x ((Curry0 p).coeff n) = 0 := by
      have hcoeffmap := congrArg (fun f => Polynomial.coeff f n) hmap
      simpa [Polynomial.coeff_map] using hcoeffmap
    have hroot :
        Polynomial.IsRoot (XCoeffEquiv ((Curry0 p).coeff n)) x := by
      simpa [Polynomial.IsRoot, hEval ((Curry0 p).coeff n)] using hcoeff0
    have hdiv :
        Polynomial.X - Polynomial.C x ∣ XCoeffEquiv ((Curry0 p).coeff n) := by
      exact (Polynomial.dvd_iff_isRoot).2 hroot
    have hdiv' :
        XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣
          XCoeffEquiv ((Curry0 p).coeff n) := by
      simpa [hX] using hdiv
    have hsymm : XCoeffEquiv.symm (XCoeffEquiv ((Curry0 p).coeff n)) =
        (Curry0 p).coeff n := by
      exact XCoeffEquiv.symm_apply_apply ((Curry0 p).coeff n)
    simpa [hsymm] using (map_dvd_iff_dvd_symm XCoeffEquiv).1 hdiv'
  have hpoly :
      Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣ Curry0 p := by
    exact (Polynomial.C_dvd_iff_dvd_coeff
      (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) (Curry0 p)).2 hcoeff_div
  have hCurry0 :
      Curry0 (CoeffLineFactor x) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) := by
    rw [Curry0, CoeffLineFactor, map_sub]
    rw [show
        (MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) by
      simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ℝ) (n := 1) (j := 0))]
    simp [MvPolynomial.finSuccEquiv_apply]
  have hdiv_curry : Curry0 (CoeffLineFactor x) ∣ Curry0 p := by
    simpa [hCurry0] using hpoly
  have hsymm_curve : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) = p := by
    rw [Curry0]
    exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply p
  have hdiv_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) :=
    (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).1 hdiv_curry
  simpa [hsymm_curve] using hdiv_symm
