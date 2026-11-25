-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitInjective_of_sClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:42:23.157899+00:00
-- url     : https://prove2.me/submissions/bc3686d0-56fb-46c3-97fe-92249f2119f8

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_diff_iff_relativeSplitInjective

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (_hC : σ.sClosure.IsClosed C) (_hxC : x ∈ C) :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x :=
  not_mem_sClosure_diff_iff_relativeSplitInjective σ C x
end PretorsionImageClosed.IndecomposableSkeleton
