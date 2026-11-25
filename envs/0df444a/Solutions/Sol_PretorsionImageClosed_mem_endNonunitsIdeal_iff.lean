-- Prove2me | solution 1 for PretorsionImageClosed.mem_endNonunitsIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:05:25.367908+00:00
-- url     : https://prove2.me/submissions/53e50086-3389-4736-88d3-484cafa26aa5

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical

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
    f ∈ endNonunitsIdeal hX hXlen ↔ ¬ IsUnit f :=
  Iff.rfl
end PretorsionImageClosed
