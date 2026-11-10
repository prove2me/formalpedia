-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_upperBCF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:21:36.746606+00:00
-- url     : https://prove2.me/submissions/d39a7e31-676f-4b70-a6d8-4db9c0fb3bc2

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      ∀ x, f x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) := by
  let f : BoundedContinuousFunction ℝ ℝ :=
   BoundedContinuousFunction.mkOfBound
      ⟨fun x => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)),
        Continuous.min continuous_const
          (Continuous.max continuous_const
            (((continuous_abs.sub continuous_const).mul continuous_const).add continuous_const))⟩
      1
      (fun x y => by
        have hbnd : ∀ z : ℝ,
            0 ≤ min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ∧
            min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 := fun z =>
          ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
        rw [Real.dist_eq]
        simp only [ContinuousMap.coe_mk]
        have hx := hbnd x; have hy := hbnd y
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  exact ⟨f, by intro x; rfl⟩
