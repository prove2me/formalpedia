-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.isGLB_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:01:26.753984+00:00
-- url     : https://prove2.me/submissions/6e25a459-983f-47a8-adf8-fe803c819a08

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf


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
omit [IsArtinianRing R] [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsGLB s ⟨Statement.Subcategory.iInf (fun Z : s => Z.1.1),
      Statement.Subcategory.IsImageClosed.iInf fun Z => Z.1.2⟩ := by
  refine ⟨fun Z hZ X hX => (Statement.Subcategory.iInf_prop_iff _ X).1 hX ⟨Z, hZ⟩,
    fun W hW X hX => ?_⟩
  exact (Statement.Subcategory.iInf_prop_iff _ X).2 fun Z => hW Z.2 X hX
end PretorsionImageClosed.IndecomposableSkeleton
