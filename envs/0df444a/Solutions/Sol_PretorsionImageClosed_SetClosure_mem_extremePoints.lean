-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.mem_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:04:23.749972+00:00
-- url     : https://prove2.me/submissions/52c84332-5d80-4340-bd67-d57ae1385e64

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} (c : SetClosure E)
variable {c}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution {C : Set E} {x : E} :
    x ∈ c.extremePoints C ↔ x ∈ C ∧ x ∉ c (C \ {x}) :=
  Iff.rfl
end PretorsionImageClosed.SetClosure
