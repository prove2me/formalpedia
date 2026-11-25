-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isGandhiSecond_gandhiSecond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:14.312752+00:00
-- url     : https://prove2.me/submissions/d3d4e47f-0e40-4f27-9733-207b0bc21681

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
theorem _root_.solution : IsGandhiSecond gandhiSecond := by
  refine ⟨rfl, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  exact ⟨_, Classical.choose_spec (exists_isDelta (X * gandhiSecond (m + 1))), rfl⟩
end PretorsionImageClosed.Statement
