-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_sClosure_diff_iff_relativeSplitInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:37.830815+00:00
-- url     : https://prove2.me/submissions/01f81f0d-0895-4688-9102-1c0155ae5433

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitMono_of_not_mem_sClosure_diff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_not_mem_sClosure_diff_of_relativeSplitInjective

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
    [IsArtinianRing (Module.End R (σ.obj x))] :
    x ∉ σ.sClosure (C \ {x}) ↔
      σ.IsRelativeSplitInjective C x := by
  constructor
  · intro hnot P
    exact splitMono_of_not_mem_sClosure_diff σ C x hnot P
  · exact not_mem_sClosure_diff_of_relativeSplitInjective σ C x
end PretorsionImageClosed.IndecomposableSkeleton
