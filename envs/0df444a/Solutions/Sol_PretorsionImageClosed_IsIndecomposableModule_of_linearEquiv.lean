-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.of_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:46:38.170358+00:00
-- url     : https://prove2.me/submissions/e8f455ff-d919-463e-bde1-28926da20495

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_bot_or_eq_bot

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]
variable {A M}
namespace PretorsionImageClosed
namespace IsIndecomposableModule
theorem _root_.solution
    {N : Type w} [AddCommMonoid N] [Module A N]
    (h : IsIndecomposableModule A M) (e : M ≃ₗ[A] N) :
    IsIndecomposableModule A N := by
  have := h.nontrivial
  refine ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ↦ ?_⟩
  simpa using h.eq_bot_or_eq_bot ((Submodule.orderIsoMapComap e.symm).isCompl hPQ)
end IsIndecomposableModule
end PretorsionImageClosed
