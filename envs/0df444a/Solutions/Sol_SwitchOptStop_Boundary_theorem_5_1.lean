-- Prove2me | solution 1 for SwitchOptStop.Boundary.theorem_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:22:34.605876+00:00
-- url     : https://prove2.me/submissions/90f0dbb9-4f69-4eff-a9d3-2493f9f71b92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value
import Theorems.Thm_SwitchOptStop_Boundary_proposition_3_7
import Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_integral_equation
import Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_uniqueness
import Theorems.Thm_SwitchOptStop_Boundary_theorem_5_1_representation

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open SwitchOptStop.Boundary

theorem solution (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S)
    (lam0 : ℝ) (hlam0 : 0 < lam0) (hlam : ∀ ι, m.lam ι = lam0) :
    Admissible m (bdry m S) ∧
    (∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 (bdry m S) ι x1) ∧
    (∀ c : Fin 2 → ℝ → ℝ, Admissible m c →
      (∀ ι : Fin 2, ∀ x1 : ℝ, 0 < x1 → SolvesIE m S lam0 c ι x1) →
      ∀ ι : Fin 2, ∀ z : ℝ, 0 < z → c ι z = bdry m S ι z) ∧
    (∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      Integrable (ieIntegrand m S lam0 (bdry m S) x) ((volume.restrict (Ioi 0)).prod (Pι S ι)) ∧
      value m S ι x =
        ∫ p, ieIntegrand m S lam0 (bdry m S) x p ∂((volume.restrict (Ioi 0)).prod (Pι S ι))) := by
  have P37 := proposition_3_7 m hQ h21 h22 hH S hS h23
  -- the boundary is nonnegative: it is an infimum of positive numbers (or `sInf ∅ = 0`)
  have hnn : ∀ ι z, 0 ≤ bdry m S ι z := fun ι z =>
    Real.sInf_nonneg (fun x hx => le_of_lt hx.1)
  refine ⟨?_, theorem_5_1_integral_equation m hQ h21 h22 hH S hS h23 lam0 hlam0 hlam,
    theorem_5_1_uniqueness m hQ h21 h22 hH S hS h23 lam0 hlam0 hlam,
    theorem_5_1_representation m hQ h21 h22 hH S hS h23 lam0 hlam0 hlam⟩
  intro ι
  obtain ⟨⟨_, _, hcont, hbdd⟩, hHnn, _, _⟩ := P37 ι
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨⟨B, fun z hz => ?_⟩, hcont, fun z hz => ⟨hnn ι z, hHnn z hz⟩⟩
  rw [abs_of_nonneg (hnn ι z)]
  exact hB ⟨z, hz, rfl⟩
