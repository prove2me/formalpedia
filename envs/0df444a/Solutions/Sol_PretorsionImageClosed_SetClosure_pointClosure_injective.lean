-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.pointClosure_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:38:56.602006+00:00
-- url     : https://prove2.me/submissions/fdf26160-8fa0-47d8-8855-79250e3c3878

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
theorem _root_.solution
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective (fun x : E ↦ c ({x} : Set E)) := by
  intro x y hxy
  change c ({x} : Set E) = c ({y} : Set E) at hxy
  by_contra hne
  have hx : x ∈ c ({y} : Set E) := by
    rw [← hxy]
    exact c.le_closure {x} (mem_singleton x)
  have hy : y ∈ c ({x} : Set E) := by
    rw [hxy]
    exact c.le_closure {y} (mem_singleton y)
  have hnot := hae hempty (by simp) (by simp) hne
    (by simpa using hx)
  exact hnot (by simpa using hy)
end PretorsionImageClosed.SetClosure
