-- Prove2me | solution 1 for contains_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:12:47.063428+00:00
-- url     : https://prove2.me/submissions/dc30a407-e46e-46c9-9972-ac5f1729de7f

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment

set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}
theorem _root_.solution (M : γ → δ → Prop) : Contains M M :=
  ⟨id, by simp [StrictMono], id, by simp [StrictMono], by aesop⟩
