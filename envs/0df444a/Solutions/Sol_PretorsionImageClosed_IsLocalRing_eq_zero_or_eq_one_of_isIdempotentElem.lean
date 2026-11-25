-- Prove2me | solution 1 for PretorsionImageClosed.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:04:42.943209+00:00
-- url     : https://prove2.me/submissions/c7580967-5b72-423c-8f95-daeaeda36511

module
public import Mathlib.RingTheory.LocalRing.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
namespace PretorsionImageClosed
namespace IsLocalRing
theorem _root_.solution
    {R : Type*} [Ring R] [IsLocalRing R] {a : R} (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  have hsum : IsUnit (a + (1 - a)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [ha, mul_one]))
  · refine Or.inl ?_
    have hidem : IsIdempotentElem (1 - a) := IsIdempotentElem.one_sub ha
    have hone : (1 : R) - a = 1 := hu.mul_left_cancel (by rw [hidem, mul_one])
    exact sub_eq_self.mp hone
end IsLocalRing
end PretorsionImageClosed
