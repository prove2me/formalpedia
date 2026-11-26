-- Prove2me | solution 1 for QuadraticFloor.ite_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:25.0638+00:00
-- url     : https://prove2.me/submissions/6b7cc976-f014-4aa0-8983-33734fd13e8d

module
public import Mathlib
public import Definitions.Def_QuadraticFloor_Defs

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]
end QuadraticFloor
