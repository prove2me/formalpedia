-- Prove2me | solution 1 for QuadraticFloor.ite_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:16.16421+00:00
-- url     : https://prove2.me/submissions/9349a6b7-80a5-4e59-ad61-9ef5bfe28baa

module
public import Mathlib
public import Definitions.Def_QuadraticFloor_Defs

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]
end QuadraticFloor
