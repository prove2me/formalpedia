-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qClosure_isConvexGeometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:36.777571+00:00
-- url     : https://prove2.me/submissions/4764c1c2-327b-4678-ac89-c3b2d1264685

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isClosed_empty


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
    σ.qClosure.IsConvexGeometry :=
  ⟨qClosure_isClosed_empty σ, qClosure_isAntiExchange σ⟩
end PretorsionImageClosed.IndecomposableSkeleton
