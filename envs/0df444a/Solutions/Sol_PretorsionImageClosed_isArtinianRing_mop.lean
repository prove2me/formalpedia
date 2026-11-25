-- Prove2me | solution 1 for PretorsionImageClosed.isArtinianRing_mop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:51:09.394243+00:00
-- url     : https://prove2.me/submissions/40c24657-e2b9-49b6-8ef6-25916709f276

module
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Definitions.Def_PretorsionImageClosed_Length_Modules

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
namespace PretorsionImageClosed
theorem _root_.solution (k : Type*) [Field k] (Λ : Type*) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] : IsArtinianRing Λᵐᵒᵖ :=
  isArtinian_of_tower k (inferInstance : IsArtinian k Λᵐᵒᵖ)
end PretorsionImageClosed
