-- Prove2me | solution 1 for PretorsionImageClosed.isArtinianRing_end_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:04:05.439578+00:00
-- url     : https://prove2.me/submissions/babded51-7a07-4b50-852a-e1192cef0c93

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_moduleEnd_of_finiteDimensional


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory
open PretorsionImageClosed
universe u
namespace PretorsionImageClosed
theorem _root_.solution (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]
    (X : FGModuleCat.{u} Λᵐᵒᵖ) :
    IsArtinianRing (Module.End Λᵐᵒᵖ X) := by
  letI : Module k X := Module.compHom X (algebraMap k Λᵐᵒᵖ)
  haveI : IsScalarTower k Λᵐᵒᵖ X :=
    ⟨fun c r x => by
      show (c • r) • x = algebraMap k Λᵐᵒᵖ c • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI : Module.Finite k X := Module.Finite.trans Λᵐᵒᵖ X
  exact isArtinianRing_moduleEnd_of_finiteDimensional (K := k)
end PretorsionImageClosed
