-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:51:53.400797+00:00
-- url     : https://prove2.me/submissions/87ab9299-c248-4fb4-b0aa-e55d2bf91a28

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_forall_isCompl

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
namespace PretorsionImageClosed
theorem _root_.solution [Nontrivial M]
    (h : ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1) :
    IsIndecomposableModule A M := by
  refine isIndecomposableModule_of_forall_isCompl fun N P hNP ↦ ?_
  rcases h (N.projection P hNP) (Submodule.isIdempotentElem_projection hNP) with h₀ | h₁
  · exact Or.inl (by simpa [h₀] using (Submodule.range_projection hNP).symm)
  · exact Or.inr (by simpa [h₁, Module.End.one_eq_id] using
      (Submodule.ker_projection hNP).symm)
end PretorsionImageClosed
