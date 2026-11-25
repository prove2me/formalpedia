-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_iff_nontrivial_and_isLocalRing_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:02.717357+00:00
-- url     : https://prove2.me/submissions/bef5db0e-80ab-40ad-849f-0c9d714f105b

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_isLocalRing_end_of_isIndecomposable
public import Theorems.Thm_PretorsionImageClosed_isIndecomposableModule_of_isLocalRing_end

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
namespace PretorsionImageClosed
theorem _root_.solution
    (hM : IsFiniteLength A M) :
    IsIndecomposableModule A M ↔ Nontrivial M ∧ IsLocalRing (Module.End A M) := by
  refine ⟨fun h ↦ ⟨h.nontrivial, isLocalRing_end_of_isIndecomposable hM h⟩,
    fun ⟨_, h⟩ ↦ ?_⟩
  have := h
  exact isIndecomposableModule_of_isLocalRing_end
end PretorsionImageClosed
