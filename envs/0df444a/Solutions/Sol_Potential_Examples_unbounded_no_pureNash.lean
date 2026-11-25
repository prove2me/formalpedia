-- Prove2me | solution 1 for Potential.Examples.unbounded_no_pureNash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:00.055542+00:00
-- url     : https://prove2.me/submissions/900d6c09-2d18-43cd-a133-61004ae5bf61

module
public import Definitions.Def_MondererShapley_Solution
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Definitions.Def_MondererShapley_Examples

set_option autoImplicit true
@[expose] public section
public section
open Potential Potential.Examples
namespace Potential.Examples
theorem _root_.solution : ¬ ∃ s, PureNash unboundedGame s := by
  rintro ⟨s, hs⟩
  have h := hs () (s () + 1)
  simp only [unboundedGame, Function.update_self] at h
  linarith
end Potential.Examples
