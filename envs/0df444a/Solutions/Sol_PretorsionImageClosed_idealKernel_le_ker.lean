-- Prove2me | solution 1 for PretorsionImageClosed.idealKernel_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:11:17.803337+00:00
-- url     : https://prove2.me/submissions/ecdfafa1-7009-4f30-bbbd-22a3913ef2e0

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
    idealKernel I ≤ LinearMap.ker f :=
  iInf_le (fun g : I ↦ LinearMap.ker
    (g : Module.End A X)) ⟨f, hf⟩
end PretorsionImageClosed
