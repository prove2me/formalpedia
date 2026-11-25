-- Prove2me | solution 1 for PretorsionImageClosed.idealRange_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:34:42.424066+00:00
-- url     : https://prove2.me/submissions/295f6a47-294d-4217-ae75-823007cd957c

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
theorem _root_.solution :
    idealRange (⊤ : Ideal (Module.End A X)) = ⊤ := by
  apply top_unique
  calc
    (⊤ : Submodule A X) = LinearMap.range
        (1 : Module.End A X) := by
          rw [Module.End.one_eq_id, LinearMap.range_id]
    _ ≤ idealRange (⊤ : Ideal (Module.End A X)) :=
      range_le_idealRange 1 (Set.mem_univ 1)
end PretorsionImageClosed
