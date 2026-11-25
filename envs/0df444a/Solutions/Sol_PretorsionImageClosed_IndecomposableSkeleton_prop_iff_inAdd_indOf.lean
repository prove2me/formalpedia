-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.prop_iff_inAdd_indOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:53:14.748649+00:00
-- url     : https://prove2.me/submissions/f59df275-3390-4b35-b547-00908f5d1c08

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.idealKernel_bot
attribute [local simp] PretorsionImageClosed.idealKernel_top
attribute [local simp] PretorsionImageClosed.idealRange_bot
attribute [local simp] PretorsionImageClosed.idealRange_top
attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff



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
theorem _root_.solution (Z : Statement.Subcategory (FGModuleCat.{w} R))
    (X : FGModuleCat.{w} R) : Z.prop X ↔ σ.InAdd (σ.indOf Z) X := by
  classical
  constructor
  · intro hX
    obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
    refine ⟨{ index := FintypeCat.of (Fin n), label := a, mem := (fun t => ?_), iso := e }⟩
    let rt : Retract (σ.obj (a t)) X :=
      { i := biproduct.ι (fun j : Fin n ↦ σ.obj (a j)) t ≫ e.inv
        r := e.hom ≫ biproduct.π (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    exact Z.prop_of_retract rt hX
  · rintro ⟨P⟩
    letI : Fintype P.index := FintypeCat.fintype
    exact Z.prop_of_iso P.iso.symm (Z.prop_biproduct _ fun t => P.mem t)
end PretorsionImageClosed.IndecomposableSkeleton
