-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.bezout
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:54:19.117365+00:00
-- url     : https://prove2.me/submissions/b6862a48-2d64-4930-b47f-91b60b2df232

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_PlaneCurveZeroSet_subset_of_dvd
import Theorems.Thm_PachDeZeeuw_Algebraic_factorized_bezout_bound

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/--
An infinite common irreducible factor gives a forbidden common curve
component.
-/
lemma noCommonCurveComponent_of_no_common_infinite_factor
    {C₁ C₂ : Set Point2} {p q : MvPolynomial (Fin 2) ℝ}
    (_hp0 : p ≠ 0) (_hq0 : q ≠ 0)
    (hC₁ : C₁ = PlaneCurveZeroSet p)
    (hC₂ : C₂ = PlaneCurveZeroSet q)
    (hno : NoCommonCurveComponent C₁ C₂) :
    ¬ HasCommonInfiniteIrreducibleFactor p q := by
  intro hcommon
  rcases hcommon with ⟨h, hirr, hinf, hp, hq⟩
  have hh0 : h ≠ 0 := hirr.ne_zero
  have hcurve : PlaneCurve.IsIrreducibleCurve h.totalDegree (PlaneCurveZeroSet h) := by
    refine ⟨h, hh0, le_rfl, hirr, rfl⟩
  have hsubset₁ : PlaneCurveZeroSet h ⊆ C₁ := by
    rw [hC₁]
    exact PlaneCurveZeroSet_subset_of_dvd hp
  have hsubset₂ : PlaneCurveZeroSet h ⊆ C₂ := by
    rw [hC₂]
    exact PlaneCurveZeroSet_subset_of_dvd hq
  exact hno ⟨h.totalDegree, PlaneCurveZeroSet h, hcurve, hinf, hsubset₁, hsubset₂⟩

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution : BezoutFiniteIntersectionStatement := by
  intro d₁ d₂
  refine ⟨(d₁ + d₂ + 1) ^ 8 + 1, Nat.succ_pos _, ?_⟩
  intro C₁ C₂ hC₁ hC₂ hno
  rcases hC₁ with ⟨p, hp0, hpdeg, hpzero⟩
  rcases hC₂ with ⟨q, hq0, hqdeg, hqzero⟩
  have hnoinf :
      ¬ HasCommonInfiniteIrreducibleFactor p q := by
    exact noCommonCurveComponent_of_no_common_infinite_factor
      hp0 hq0 hpzero hqzero hno
  have hbound := factorized_bezout_bound (d₁ := d₁) (d₂ := d₂) p q hp0 hq0 hpdeg hqdeg hnoinf
  have hfinite : (C₁ ∩ C₂).Finite := by
    rw [hpzero, hqzero]
    exact hbound.1
  refine ⟨hfinite, ?_⟩
  have hle : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤ (d₁ + d₂ + 1) ^ 8 + 1 := by
    exact Nat.le_trans hbound.2 (Nat.le_succ _)
  rw [hpzero, hqzero]
  exact hle
