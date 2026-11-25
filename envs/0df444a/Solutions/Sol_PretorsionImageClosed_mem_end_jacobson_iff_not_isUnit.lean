-- Prove2me | solution 1 for PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:50.06554+00:00
-- url     : https://prove2.me/submissions/5e991569-5373-4144-b04a-7fb7189e15bd

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_end_jacobson_eq_nonunits

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
namespace PretorsionImageClosed
theorem _root_.solution
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X)
    (f : Module.End A X) :
    f ∈ Ring.jacobson (Module.End A X) ↔ ¬ IsUnit f := by
  rw [end_jacobson_eq_nonunits hX hXlen]
  rfl
end PretorsionImageClosed
