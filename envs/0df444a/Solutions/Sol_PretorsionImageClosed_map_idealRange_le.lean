-- Prove2me | solution 1 for PretorsionImageClosed.map_idealRange_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:34:43.197532+00:00
-- url     : https://prove2.me/submissions/d5a1e977-ff17-492c-bac5-05b82df2948f

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_range_le_idealRange

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
    {I J : Ideal (Module.End A X)}
    (f : Module.End A X) (hf : f ∈ I) :
    Submodule.map f (idealRange J) ≤ idealRange (I * J) := by
  rw [idealRange, Submodule.map_iSup]
  apply iSup_le
  rintro ⟨g, hg⟩
  rw [← LinearMap.range_comp, ← Module.End.mul_eq_comp]
  exact range_le_idealRange (f * g)
    (Ideal.mul_mem_mul hf hg)
end PretorsionImageClosed
