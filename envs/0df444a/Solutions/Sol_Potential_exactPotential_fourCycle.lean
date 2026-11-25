-- Prove2me | solution 1 for Potential.exactPotential_fourCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:52:42.165296+00:00
-- url     : https://prove2.me/submissions/2bdef9b8-0539-4432-990b-2a5a6e55246c

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

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) : FourCycle u := by
  intro s i j hij a b
  have h1 := hp s i a
  have h2 := hp (Function.update s i a) j b
  have h3 := hp (Function.update s j b) i a
  have h4 := hp s j b
  rw [← Function.update_comm hij a b s] at h3
  linarith
end Potential
