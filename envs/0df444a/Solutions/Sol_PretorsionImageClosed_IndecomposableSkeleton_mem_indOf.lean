-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.mem_indOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:44:55.408566+00:00
-- url     : https://prove2.me/submissions/d3683b4f-cdd6-4b93-a16c-e9dbfc0c8b18

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories

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
theorem _root_.solution {Z : Statement.Subcategory (FGModuleCat.{w} R)} {i : ι} :
    i ∈ σ.indOf Z ↔ Z.prop (σ.obj i) := Iff.rfl
end PretorsionImageClosed.IndecomposableSkeleton
