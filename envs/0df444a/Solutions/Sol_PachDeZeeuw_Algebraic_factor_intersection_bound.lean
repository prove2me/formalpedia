-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.factor_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:50:30.771631+00:00
-- url     : https://prove2.me/submissions/e3bfc849-8a49-4de8-8a5c-5c29c30a4b84

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_curry_isPrimitive_of_irreducible_positive_natDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_curry_isRelPrime_of_nonassociated_irreducibles
import Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_degree_le
import Theorems.Thm_PachDeZeeuw_Algebraic_normalized_factor_irreducible
import Theorems.Thm_PachDeZeeuw_Algebraic_primitive_nonvertical_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_totalDegree_pderiv_le
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_nonvertical_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_zeroCurry_pair_intersection_bound

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- The primitive pair bound for equal degree parameters fits under the fourth power of `d + 1`. -/
lemma primitive_bound_le_fourth_succ (d : ℕ) :
    (((d + d) ^ 2 + 1) * d : ℕ) ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])

/-- A quadratic bound fits under the fourth power of `d + 1`. -/
lemma mul_self_le_fourth_succ (d : ℕ) : d * d ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution {d : ℕ} (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    {k : PlanePoly}
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h))
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
  classical
  have hkirr : Irreducible k :=
    normalized_factor_irreducible (p := MvPolynomial.pderiv i h) hk
  have hkdeg : k.totalDegree ≤ d := by
    calc
      k.totalDegree ≤ (MvPolynomial.pderiv i h).totalDegree :=
        normalized_factor_degree_le (p := MvPolynomial.pderiv i h) (h := k) hpi hk
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hbound :=
        zeroCurry_zeroCurry_pair_intersection_bound
          (B := (d + 1) ^ 4) h k hh hkirr hnot hdeg0 hkdeg0
      simpa using hbound
    · have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hkirr hdeg hkdeg hnot hdeg0 hkpos
      exact ⟨hbound.1, le_trans hbound.2 (mul_self_le_fourth_succ d)⟩
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hnot' : ¬ Associated k h := by
        intro hassoc
        exact hnot hassoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hkirr hh hkdeg hdeg hnot' hkdeg0 hpos
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d * d := by
        simpa [Set.inter_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (mul_self_le_fourth_succ d)⟩
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hkirr hkpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hkirr hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg hkdeg hprim kprim hpos hkpos hrel
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ ((d + d) ^ 2 + 1) * d := by
        simpa using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (primitive_bound_le_fourth_succ d)⟩
