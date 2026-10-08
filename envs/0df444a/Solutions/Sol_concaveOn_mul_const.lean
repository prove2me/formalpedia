-- Prove2me | solution 1 for concaveOn_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:24:49.413279+00:00
-- url     : https://prove2.me/submissions/c89a9365-4023-4ea3-873e-0f6eb82f6b47

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (c : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun s => c * s) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  have hEq : c * (u * x + v * y) = u * (c * x) + v * (c * y) := by ring
  nlinarith [hEq]
