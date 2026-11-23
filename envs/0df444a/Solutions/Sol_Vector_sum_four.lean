-- Prove2me | solution 1 for Vector.sum_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:39:40.465254+00:00
-- url     : https://prove2.me/submissions/3e76686e-ab7b-4155-8efb-6b5af34124b8

module
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
public import Definitions.Def_Apportionmentlib_Utils

set_option autoImplicit false
@[expose] public section
public section
namespace Vector
theorem _root_.solution (v : Vector ℕ 4) : v.sum = v[0] + v[1] + v[2] + v[3] := by
  have : v.toArray = #[v[0], v[1], v[2], v[3]] := by grind
  simp [Vector.sum, this, Array.sum]
  abel
end Vector
