-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.eq_iff_nonempty_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:04.271913+00:00
-- url     : https://prove2.me/submissions/3fe872d1-6b19-474b-9307-0f579f976c48

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.HopkinsLevitzki
public import Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
open PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {i j : ι} :
    i = j ↔ Nonempty (σ.obj i ≅ σ.obj j) := by
  constructor
  · rintro rfl
    exact ⟨Iso.refl _⟩
  · exact σ.eq_of_iso
end PretorsionImageClosed.IndecomposableSkeleton
