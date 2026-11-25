-- Prove2me | solution 1 for Potential.simpleClosedPaths_simpleFourCycles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:44.946795+00:00
-- url     : https://prove2.me/submissions/87252bac-3893-445a-a1ad-93f93454d349

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
theorem _root_.solution (u : Payoff A)
    (h : SimpleClosedPathProperty u) : SimpleFourCycleProperty u := by
  intro s ms he hn _
  exact h s ms he hn
end Potential
