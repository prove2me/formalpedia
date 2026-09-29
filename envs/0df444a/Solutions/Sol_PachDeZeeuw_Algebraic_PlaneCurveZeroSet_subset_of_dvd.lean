-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.PlaneCurveZeroSet_subset_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:50.200653+00:00
-- url     : https://prove2.me/submissions/4c811ad1-d581-462d-8ce0-08846fb13b87

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_PlaneCurveZeroSet

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {p q : MvPolynomial (Fin 2) ℝ}
    (hpq : p ∣ q) : PlaneCurveZeroSet p ⊆ PlaneCurveZeroSet q := by
  intro x hx
  rcases hpq with ⟨r, rfl⟩
  rw [mem_PlaneCurveZeroSet] at hx ⊢
  simp [MvPolynomial.eval_mul, hx]
