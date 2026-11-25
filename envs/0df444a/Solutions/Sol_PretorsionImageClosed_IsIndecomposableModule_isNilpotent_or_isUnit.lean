-- Prove2me | solution 1 for PretorsionImageClosed.IsIndecomposableModule.isNilpotent_or_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:56:27.395126+00:00
-- url     : https://prove2.me/submissions/2d86baaf-782d-434b-a712-cec5446d089a

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_isNilpotent_or_bijective

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
    IsNilpotent f ∨ IsUnit f :=
  (h.isNilpotent_or_bijective f).imp id (Module.End.isUnit_iff f).mpr
end IsIndecomposableModule
end PretorsionImageClosed
