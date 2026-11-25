-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.splitting_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:04.728718+00:00
-- url     : https://prove2.me/submissions/8bb25180-bd8f-4d8a-a4ee-0266b3451ee8

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitting_eq_extremePoints
public import Theorems.Thm_PretorsionImageClosed_SetClosure_extremePoints_subset_of_closure_eq


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
theorem _root_.solution {Z : Statement.Subcategory (FGModuleCat.{w} R)} {S : Set ι}
    (hS : σ.iClosure S = σ.indOf Z) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} ⊆ S := by
  rw [splitting_eq_extremePoints]
  exact SetClosure.extremePoints_subset_of_closure_eq hS
end PretorsionImageClosed.IndecomposableSkeleton
