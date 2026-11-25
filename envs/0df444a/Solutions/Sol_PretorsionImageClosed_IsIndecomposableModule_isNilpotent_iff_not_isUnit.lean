-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.isNilpotent_iff_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:42.273804+00:00
-- url     : https://prove2.me/submissions/9e53f21e-3fa8-41a9-a182-5889f08a0a70

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_isNilpotent_or_isUnit

set_option autoImplicit true
@[expose] public section
public section
open PretorsionImageClosed
universe u v w
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
variable [IsNoetherian A M] [IsArtinian A M]
namespace PretorsionImageClosed
namespace IsIndecomposableModule
theorem _root_.solution
    (h : IsIndecomposableModule A M) (f : Module.End A M) :
    IsNilpotent f ↔ ¬ IsUnit f := by
  have := h.nontrivial
  exact ⟨IsNilpotent.not_isUnit, (h.isNilpotent_or_isUnit f).resolve_right⟩
end IsIndecomposableModule
end PretorsionImageClosed
