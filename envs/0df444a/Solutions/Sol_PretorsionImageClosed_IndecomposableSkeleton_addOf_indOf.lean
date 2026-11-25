-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.addOf_indOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:19.742053+00:00
-- url     : https://prove2.me/submissions/93c922ff-81de-4ee6-ae79-3bddd3d373b4

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_prop_iff_inAdd_indOf

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    σ.addOf (σ.indOf Z) = Z := by
  apply Statement.Subcategory.ext
  funext X
  exact propext (σ.prop_iff_inAdd_indOf Z X).symm
end PretorsionImageClosed.IndecomposableSkeleton
