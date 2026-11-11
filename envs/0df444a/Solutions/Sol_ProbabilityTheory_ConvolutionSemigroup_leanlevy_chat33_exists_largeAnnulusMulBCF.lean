-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeAnnulusMulBCF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:35:25.200753+00:00
-- url     : https://prove2.me/submissions/012eafe2-4b49-4b44-9a35-ee47e82481a7

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_exists_annulusBCF
import Mathlib.Tactic.Positivity
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      (∀ x, f x = max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) * g x) ∧
      (∀ x, |f x| ≤ M) := by
  obtain ⟨u, hu⟩ :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF ρ hρ n
  have hU : ∀ z : ℝ, 0 ≤ u z ∧ u z ≤ 1 := by
    intro z
    rw [hu z]
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ)) := by positivity
    linarith
  have hbnd : ∀ z, |u z * g z| ≤ M := fun z => by
    rw [abs_mul, abs_of_nonneg (hU z).1]
    calc u z * |g z|
        ≤ 1 * |g z| :=
          mul_le_mul_of_nonneg_right (hU z).2 (abs_nonneg _)
      _ ≤ 1 * M := mul_le_mul_of_nonneg_left (hg_bnd z) zero_le_one
      _ = M := one_mul _
  let φ : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => u x * g x, u.continuous.mul hg_cont⟩
      (2 * M)
      (fun x y => by
        simp only [ContinuousMap.coe_mk]
        rw [Real.dist_eq]
        have hx := hbnd x
        have hy := hbnd y
        rw [abs_le] at hx hy
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  refine ⟨φ, ?_, ?_⟩
  · intro x
    change u x * g x = max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) * g x
    rw [hu x]
  · intro x
    change |u x * g x| ≤ M
    exact hbnd x
