-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:23.806037+00:00
-- url     : https://prove2.me/submissions/5164b892-f305-46b3-84f2-cc5c450d4676

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_zero_or_eq_one_of_isIdempotentElem
public import Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_forall_isIdempotentElem
public import Theorems.Thm_PretorsionImageClosed_IsLocalRing_eq_zero_or_eq_one_of_isIdempotentElem


set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
namespace PretorsionImageClosed
theorem _root_.solution :
    IsIndecomposableModule A M ↔
      Nontrivial M ∧ ∀ f : Module.End A M, IsIdempotentElem f → f = 0 ∨ f = 1 :=
  ⟨fun h ↦ ⟨h.nontrivial, fun _ hf ↦ h.eq_zero_or_eq_one_of_isIdempotentElem hf⟩,
    fun ⟨_, h⟩ ↦ isIndecomposableModule_of_forall_isIdempotentElem h⟩
end PretorsionImageClosed
