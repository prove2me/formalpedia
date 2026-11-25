-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.splitting_eq_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:11.576133+00:00
-- url     : https://prove2.me/submissions/62670e26-fcc3-43f0-ae68-ef99e71fe9e9

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_extremePoints_iff_splitting
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
variable [IsArtinianRing R]
variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
omit [IsArtinianRing R]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.iClosure.extremePoints (σ.indOf Z) := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact (σ.extremePoints_iff_splitting hx).2 h
  · intro h
    exact ⟨h.1, (σ.extremePoints_iff_splitting h.1).1 h⟩
end PretorsionImageClosed.IndecomposableSkeleton
