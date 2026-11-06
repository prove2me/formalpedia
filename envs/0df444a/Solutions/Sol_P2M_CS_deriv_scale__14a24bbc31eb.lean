-- Prove2me | solution 1 for P2M_CS_deriv_scale__14a24bbc31eb
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:00:06.713925+00:00
-- url     : https://prove2.me/submissions/ea64d1ca-afb8-45a8-b398-9536236c14c8

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}

theorem solution {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  by_cases h : R = 0
  · subst R
    simp [CS.deriv, CS.scale]
  · simp only [CS.deriv, CS.scale, h, ↓reduceDIte, funscale]
    simpa only [smul_eq_mul] using
      (deriv_comp_mul_left (c := R⁻¹) (f := fun x : ℝ => f x) (x := v))
