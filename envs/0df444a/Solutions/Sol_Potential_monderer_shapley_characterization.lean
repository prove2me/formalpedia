-- Prove2me | solution 1 for Potential.monderer_shapley_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:49.661915+00:00
-- url     : https://prove2.me/submissions/bb945bcc-dc16-4871-bf88-4e36ed8e7afa

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_fourCycle_exists_exactPotential
public import Theorems.Thm_Potential_closedPaths_simpleClosedPaths
public import Theorems.Thm_Potential_simpleClosedPaths_simpleFourCycles
public import Theorems.Thm_Potential_simpleFourCycles_fourCycle
public import Theorems.Thm_Potential_monderer_shapley_fourCycle
public import Theorems.Thm_Potential_monderer_shapley_closedPaths

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
namespace Potential
theorem _root_.solution (u : Payoff A) :
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ ClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleFourCycleProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ FourCycle u) := by
  refine ⟨monderer_shapley_closedPaths u, ?_, ?_, monderer_shapley_fourCycle u⟩
  · constructor
    · intro h
      exact closedPaths_simpleClosedPaths u ((monderer_shapley_closedPaths u).mp h)
    · intro h
      exact fourCycle_exists_exactPotential u
        (simpleFourCycles_fourCycle u (simpleClosedPaths_simpleFourCycles u h))
  · constructor
    · intro h
      exact simpleClosedPaths_simpleFourCycles u
        (closedPaths_simpleClosedPaths u ((monderer_shapley_closedPaths u).mp h))
    · intro h
      exact fourCycle_exists_exactPotential u (simpleFourCycles_fourCycle u h)
end Potential
