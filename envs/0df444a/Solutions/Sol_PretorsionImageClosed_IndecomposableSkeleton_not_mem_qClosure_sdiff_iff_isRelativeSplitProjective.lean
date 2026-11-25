-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:48.008448+00:00
-- url     : https://prove2.me/submissions/dc7f0264-0902-4613-a270-72ce48371c46

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_isRelativeSplitProjective_of_not_mem_qClosure_sdiff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_qClosure_sdiff_of_isRelativeSplitProjective

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
    [IsArtinianRing (Module.End R (σ.obj x))] :
    x ∉ σ.qClosure (C \ {x}) ↔
      σ.IsRelativeSplitProjective C x :=
  ⟨σ.isRelativeSplitProjective_of_not_mem_qClosure_sdiff C x,
    σ.not_mem_qClosure_sdiff_of_isRelativeSplitProjective C x⟩
end PretorsionImageClosed.IndecomposableSkeleton
