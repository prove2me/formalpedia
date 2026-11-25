-- Prove2me | solution 1 for Potential.monderer_shapley_fourCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:37.134721+00:00
-- url     : https://prove2.me/submissions/988fd49a-e4f3-4e80-82d3-e91b84400567

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
public import Theorems.Thm_Potential_exactPotential_fourCycle

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
namespace Potential
theorem _root_.solution (u : Payoff A) :
    (∃ P : Profile A → ℝ, ExactPotential u P) ↔ FourCycle u := by
  constructor
  · rintro ⟨P, hp⟩
    exact exactPotential_fourCycle u P hp
  · exact fourCycle_exists_exactPotential u
end Potential
