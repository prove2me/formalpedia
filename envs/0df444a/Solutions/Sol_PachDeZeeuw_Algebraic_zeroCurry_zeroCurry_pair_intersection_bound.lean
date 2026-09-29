-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.zeroCurry_zeroCurry_pair_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:59.79548+00:00
-- url     : https://prove2.me/submissions/98eb0fa9-55f3-4636-b739-32f81f55256b

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_curry_natDegree_zero_root
import Theorems.Thm_PachDeZeeuw_Algebraic_not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
import Theorems.Thm_PachDeZeeuw_Algebraic_planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- If the coefficient roots have empty intersection, the corresponding coefficient-line
intersections are empty. -/
theorem coeffline_coeffline_pair_intersection_empty_of_no_common_real_root
    (a b : XCoeff)
    (hnoRoot : CoeffRootSet a ∩ CoeffRootSet b = ∅) :
    CoeffLineZeroSet a ∩ CoeffLineZeroSet b = ∅ := by
  ext z
  constructor
  · intro hz
    have hx : coeffCoord z ∈ CoeffRootSet a ∩ CoeffRootSet b := by
      simpa [CoeffLineZeroSet, CoeffRootSet, coeffCoord] using hz
    have hfalse : False := by
      simp [hnoRoot] at hx
    exact False.elim hfalse
  · intro hz
    cases hz

/-- The zero-degree / zero-degree coefficient-line case is empty. -/
lemma no_common_coeff_root_of_zero_curry_nonassociated
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    CoeffRootSet ((Curry0 h).coeff 0) ∩ CoeffRootSet ((Curry0 k).coeff 0) = ∅ := by
  ext x
  constructor
  · intro hx
    have hroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0 := hx.1
    have hdivk : ¬ CoeffLineFactor x ∣ k :=
      not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated h k hh hk hnot hdeg0 hroot
    have hdivk' : CoeffLineFactor x ∣ k :=
      coeffLineFactor_dvd_of_curry_natDegree_zero_root k kdeg0 hx.2
    exact False.elim (hdivk hdivk')
  · intro hx
    cases hx

/-- The zero-degree / zero-degree plane intersection is empty. -/
lemma zeroCurry_zeroCurry_pair_intersection_empty
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k = ∅ := by
  have hnoRoot :
      CoeffRootSet ((Curry0 h).coeff 0) ∩ CoeffRootSet ((Curry0 k).coeff 0) = ∅ := by
    exact no_common_coeff_root_of_zero_curry_nonassociated h k hh hk hnot hdeg0 kdeg0
  rw [planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero h hdeg0,
    planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero k kdeg0]
  exact coeffline_coeffline_pair_intersection_empty_of_no_common_real_root _ _ hnoRoot

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h k : MvPolynomial (Fin 2) ℝ)
    {B : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ B := by
  have hempty : PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k = ∅ :=
    zeroCurry_zeroCurry_pair_intersection_empty h k hh hk hnot hdeg0 kdeg0
  refine ⟨by simp [hempty], ?_⟩
  simp [hempty]
