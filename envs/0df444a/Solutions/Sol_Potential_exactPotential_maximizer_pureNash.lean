-- Prove2me | solution 1 for Potential.exactPotential_maximizer_pureNash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:02:05.524816+00:00
-- url     : https://prove2.me/submissions/44425b15-b204-4d6a-bf3b-51b6fad995f3

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
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
omit [Fintype I] [∀ i, Nonempty (A i)]
namespace Potential
theorem _root_.solution (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (hs : ∀ t, P t ≤ P s) : PureNash u s := by
  intro i a
  have he := hp s i a
  have hm := hs (Function.update s i a)
  linarith
end Potential
