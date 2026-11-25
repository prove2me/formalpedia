-- Prove2me | solution 1 for PretorsionImageClosed.IsSimpleModule.isIndecomposableModule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:26.264804+00:00
-- url     : https://prove2.me/submissions/a947b7a6-2fd4-46ed-af26-c35eeb4d58e8

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
namespace PretorsionImageClosed
namespace IsSimpleModule
theorem _root_.solution [IsSimpleModule A M] :
    IsIndecomposableModule A M := by
  refine ⟨IsSimpleModule.nontrivial A M, fun N P hNP ↦ ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · exact Or.inl hN
  · refine Or.inr ?_
    have hdisj : Disjoint (⊤ : Submodule A M) P := hN ▸ hNP.disjoint
    simpa using hdisj
end IsSimpleModule
end PretorsionImageClosed
