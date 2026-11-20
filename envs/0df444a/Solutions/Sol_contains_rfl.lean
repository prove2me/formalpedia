-- Prove2me | solution 1 for contains_rfl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:14:21.700171+00:00
-- url     : https://prove2.me/submissions/1ab213a8-ad5e-4ad3-b8f9-59eb19609f04

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Theorems.Thm_contains_refl
attribute [local refl] contains_refl

set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}
theorem _root_.solution {M : γ → δ → Prop} : Contains M M := by exact contains_refl M
