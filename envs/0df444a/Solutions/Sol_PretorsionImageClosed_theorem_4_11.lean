-- Prove2me | solution 1 for PretorsionImageClosed.theorem_4_11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:14:04.543044+00:00
-- url     : https://prove2.me/submissions/dae4c458-aea2-47ec-a6ff-631234d97f19

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ImageClosure
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_FiniteDimensionalAlgebras
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_end_mod
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isClosed_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_iClosure_isFinitary
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_mop


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory
open PretorsionImageClosed
universe u
namespace PretorsionImageClosed
theorem _root_.solution (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    (modSkeleton k Λ).iClosure.IsFinitary ∧ (modSkeleton k Λ).iClosure.IsConvexGeometry ∧
      ∀ Z : Statement.Subcategory (Statement.Mod k Λ),
        Z.IsImageClosed ↔ (modSkeleton k Λ).iClosure.IsClosed ((modSkeleton k Λ).indOf Z) := by
  haveI := Statement.isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  haveI : ∀ i, IsArtinianRing (Module.End Λᵐᵒᵖ ((modSkeleton k Λ).obj i)) :=
    fun i => isArtinianRing_end_mod k Λ _
  exact ⟨(modSkeleton k Λ).iClosure_isFinitary,
    ⟨(modSkeleton k Λ).iClosure_isClosed_empty,
      (modSkeleton k Λ).iClosure_isAntiExchange (modSkeleton k Λ).qClosure_isAntiExchange
        (modSkeleton k Λ).sClosure_isAntiExchange⟩,
    fun Z => (modSkeleton k Λ).isImageClosed_iff_isClosed_indOf Z⟩
end PretorsionImageClosed
