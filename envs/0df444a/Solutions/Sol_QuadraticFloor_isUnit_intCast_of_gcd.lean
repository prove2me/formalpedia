-- Prove2me | solution 1 for QuadraticFloor.isUnit_intCast_of_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:06.17453+00:00
-- url     : https://prove2.me/submissions/efc19fc2-0899-4f96-a300-f560d25c7b23

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} {B : ℤ} (h : Int.gcd B A = 1) : IsUnit (B : ZMod A) := by
  have hc : Nat.Coprime B.natAbs A := by rw [Int.gcd_eq_natAbs] at h; simpa using h
  rcases Int.natAbs_eq B with hB | hB
  · rw [hB, Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime _ _).2 hc
  · rw [hB, Int.cast_neg, Int.cast_natCast]; exact ((ZMod.isUnit_iff_coprime _ _).2 hc).neg
end QuadraticFloor
