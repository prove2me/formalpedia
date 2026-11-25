-- Prove2me | solution 1 for PretorsionImageClosed.idealKernel_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:12:19.024199+00:00
-- url     : https://prove2.me/submissions/a94e2632-e8d7-4115-aae6-8d9d6c6f41d8

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_idealKernel_le_ker

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
    idealKernel (⊤ : Ideal (Module.End A X)) = ⊥ := by
  apply bot_unique
  calc
    idealKernel (⊤ : Ideal (Module.End A X)) ≤
        LinearMap.ker (1 : Module.End A X) :=
      idealKernel_le_ker 1 (Set.mem_univ 1)
    _ = ⊥ := by
      rw [Module.End.one_eq_id, LinearMap.ker_id]
end PretorsionImageClosed
