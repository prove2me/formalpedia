-- Prove2me | solution 1 for PretorsionImageClosed.range_le_idealRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:30:02.016513+00:00
-- url     : https://prove2.me/submissions/6034bba9-cb1d-4934-a3ce-ed6efc0e9440

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
    {I : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    LinearMap.range f ≤ idealRange I :=
  le_iSup (fun g : I ↦ LinearMap.range
    (g : Module.End A X)) ⟨f, hf⟩
end PretorsionImageClosed
