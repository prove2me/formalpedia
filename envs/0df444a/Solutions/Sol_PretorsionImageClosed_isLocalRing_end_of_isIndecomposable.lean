-- Prove2me | solution 1 for PretorsionImageClosed.isLocalRing_end_of_isIndecomposable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:01:01.761659+00:00
-- url     : https://prove2.me/submissions/db677c9e-c785-4954-a0e8-f81413bdcafe

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
namespace PretorsionImageClosed
theorem _root_.solution
    (hM : IsFiniteLength A M) (h : IsIndecomposableModule A M) :
    IsLocalRing (Module.End A M) := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have := h.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  exact (h.isNilpotent_or_isUnit f).symm.imp id IsNilpotent.isUnit_one_sub
end PretorsionImageClosed
