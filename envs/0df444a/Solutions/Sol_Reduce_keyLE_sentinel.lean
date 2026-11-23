-- Prove2me | solution 1 for Reduce.keyLE_sentinel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:13:17.312691+00:00
-- url     : https://prove2.me/submissions/e2633271-64f2-432f-9614-909536d41eff

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution (a : RawPointer × RawPointer) :
    KeyLE ((.inl false : RawPointer), (.inl false : RawPointer)) a := by
  -- `.inl false` is the least `RawPointer`.  The `@LE.le RawPointer` pins our lex order
  -- (not the ambient pointwise `Sum.instLESum`, which the bare `.inl` literal would select).
  have hbot : ∀ x : RawPointer, @LE.le RawPointer _ (.inl false) x := by
    rintro (b | c)
    · exact Sum.Lex.inl (by cases b <;> decide)
    · exact Sum.Lex.sep _ _
  unfold KeyLE leKeyPair
  split
  · exact decide_eq_true (hbot a.2)
  · exact decide_eq_true (hbot a.1)
end Reduce
