-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:21:33.616036+00:00
-- url     : https://prove2.me/submissions/80aa3745-43e5-4f6f-b42a-8f4636c566ca

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.Positivity
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      ∀ x, f x = max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) := by
  let f : BoundedContinuousFunction ℝ ℝ :=
   BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))),
        Continuous.max continuous_const
          (continuous_const.sub (continuous_const.mul
            (Continuous.max continuous_const
              ((continuous_abs.comp (continuous_abs.sub continuous_const)).sub continuous_const))))⟩
      1
      (fun x y => by
        have hbnd : ∀ z : ℝ,
            0 ≤ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ∧
            max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ≤ 1 := fun z => by
          refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
          have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ)) := by positivity
          linarith
        rw [Real.dist_eq]
        simp only [ContinuousMap.coe_mk]
        have hx := hbnd x; have hy := hbnd y
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  exact ⟨f, by intro x; rfl⟩
