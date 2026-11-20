-- Prove2me | solution 1 for contains_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:13:35.5362+00:00
-- url     : https://prove2.me/submissions/653d3a93-1247-43db-9098-9e45fa51b6ba

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
theorem _root_.solution [IsEmpty α] [IsEmpty β] : Contains P M := by
   simp [Contains, StrictMono]
