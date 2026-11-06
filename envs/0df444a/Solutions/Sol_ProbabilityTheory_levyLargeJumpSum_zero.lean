-- Prove2me | solution 1 for ProbabilityTheory.levyLargeJumpSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:01:53.566784+00:00
-- url     : https://prove2.me/submissions/3d5d2298-2d6b-4aa2-be07-a2f577908ebe

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory Set

theorem solution : ∀ {Ω : Type} {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → Prod Real Real} (ω : Ω),
  @Eq Real
    (@ProbabilityTheory.levyLargeJumpSum Ω K X (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ω)
    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) := by
  intro Ω K X ω
  have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      fun p : ℝ × ℝ => p.2) = fun _ => 0 := by
    rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
  simp only [ProbabilityTheory.levyLargeJumpSum, hband, ProbabilityTheory.pieceSum,
    Finset.sum_const_zero, tsum_zero]
