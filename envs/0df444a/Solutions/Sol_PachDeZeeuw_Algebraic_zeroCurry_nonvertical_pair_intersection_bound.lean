-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:49:08.448308+00:00
-- url     : https://prove2.me/submissions/2a22f3d7-dc3e-4588-839d-ed30150f7d70

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffline_nonvertical_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
import Theorems.Thm_PachDeZeeuw_Algebraic_planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- The constant coefficient of a curry has total degree at most the original polynomial. -/
lemma coeff_zero_totalDegree_le
    (h : MvPolynomial (Fin 2) ℝ) :
    ((Curry0 h).coeff 0) ≠ 0 →
      ((Curry0 h).coeff 0).totalDegree ≤ h.totalDegree := by
  intro h0
  have hle :=
    MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := ℝ) (n := 1) h 0 h0
  simpa [Curry0] using hle

/-- A zero-degree curry has nonzero constant coefficient when the polynomial is nonzero. -/
lemma coeff_zero_ne_zero_of_curry_natDegree_zero
    (h : MvPolynomial (Fin 2) ℝ)
    (hh0 : h ≠ 0)
    (hdeg0 : (Curry0 h).natDegree = 0) :
    (Curry0 h).coeff 0 ≠ 0 := by
  intro hzero
  have hC : Curry0 h = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, hzero]
    simp
  exact hh0 (by
    apply (MvPolynomial.finSuccEquiv ℝ 1).injective
    simpa [Curry0] using hC)

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h k : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kpos : 0 < (Curry0 k).natDegree) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by
  have hzero : ((Curry0 h).coeff 0) ≠ 0 := by
    exact coeff_zero_ne_zero_of_curry_natDegree_zero h hh.ne_zero hdeg0
  have hcoeffdeg : ((Curry0 h).coeff 0).totalDegree ≤ d₁ := by
    exact le_trans (coeff_zero_totalDegree_le h hzero) hdeg
  have hnotDiv :
      ∀ x : ℝ,
        MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0 →
          ¬ CoeffLineFactor x ∣ k := by
    intro x hxroot
    exact not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated h k hh hk hnot hdeg0 hxroot
  have hline :
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k) =
        (CoeffLineZeroSet ((Curry0 h).coeff 0) ∩ PlaneCurveZeroSet k) := by
    rw [planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero h hdeg0]
  simpa [hline] using
    (coeffline_nonvertical_pair_intersection_bound ((Curry0 h).coeff 0) k hzero hk.ne_zero
      hcoeffdeg kdeg kpos hnotDiv)
