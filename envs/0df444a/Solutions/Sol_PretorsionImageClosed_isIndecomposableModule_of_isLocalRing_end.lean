-- Prove2me | solution 1 for PretorsionImageClosed.isIndecomposableModule_of_isLocalRing_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:57:34.829792+00:00
-- url     : https://prove2.me/submissions/0a3a58c1-dbfc-4500-82c7-c85b02516296

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
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
theorem _root_.solution [Nontrivial M]
    [IsLocalRing (Module.End A M)] : IsIndecomposableModule A M :=
  isIndecomposableModule_of_forall_isIdempotentElem fun _ hf ↦
    IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hf
end PretorsionImageClosed
