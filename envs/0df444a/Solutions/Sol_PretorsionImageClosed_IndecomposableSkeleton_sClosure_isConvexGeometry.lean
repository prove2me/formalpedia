-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:44.516846+00:00
-- url     : https://prove2.me/submissions/8f5ef933-38ea-4ab3-8b9b-71e09fcf2522

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isClosed_empty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] :
    σ.sClosure.IsConvexGeometry :=
  ⟨sClosure_isClosed_empty σ, sClosure_isAntiExchange σ⟩
end PretorsionImageClosed.IndecomposableSkeleton
