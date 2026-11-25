-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.extremal_iff_isRelativeSplitProjective_of_qClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:05:58.192128+00:00
-- url     : https://prove2.me/submissions/6b8a028c-fd8b-4e69-a46e-4898ace9d55d

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_iff_isRelativeSplitProjective

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
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (_hC : σ.qClosure.IsClosed C) (_hxC : x ∈ C) :
    x ∉ σ.qClosure (C \ {x}) ↔
      σ.IsRelativeSplitProjective C x :=
  σ.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective C x
end PretorsionImageClosed.IndecomposableSkeleton
