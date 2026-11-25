-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.range_le_trace_sdiff_sup_idealRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:16.428517+00:00
-- url     : https://prove2.me/submissions/7cb16d69-a8a2-410e-88f9-7f8c9f6cd4ed

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_map_apply_eq_sum_components
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_not_isUnit_component_of_not_isSplitEpi
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_range_le_trace_of_mem
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_mem_end_jacobson_iff_not_isUnit
public import Theorems.Thm_PretorsionImageClosed_range_le_idealRange
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
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
open PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
namespace PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
theorem _root_.solution
    {C : Set ι} {x : ι}
    (P : σ.FacPresentation C (σ.obj x))
    (hP : ¬ IsSplitEpi P.map) :
    LinearMap.range P.map.hom.hom ≤
      σ.trace (C \ {x}) (σ.obj x) ⊔
        PretorsionImageClosed.idealRange
          (Ring.jacobson (Module.End R (σ.obj x))) := by
  letI : Fintype P.index := FintypeCat.fintype
  rintro z ⟨a, rfl⟩
  rw [P.map_apply_eq_sum_components σ a]
  apply Submodule.sum_mem
  intro t _
  by_cases ht : P.label t = x
  · let f : σ.obj x ⟶ σ.obj x :=
      eqToHom (congrArg σ.obj ht.symm) ≫ P.component σ t
    have hfRad :
        f.hom.hom ∈
          Ring.jacobson (Module.End R (σ.obj x)) := by
      apply
        (PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
          (σ.indecomposable x) (σ.finiteLength x) f.hom.hom).2
      exact P.not_isUnit_component_of_not_isSplitEpi σ hP t ht
    have hrange :
        LinearMap.range (P.component σ t).hom.hom ≤
          LinearMap.range f.hom.hom := by
      let e : σ.obj x ≅ σ.obj (P.label t) :=
        eqToIso (congrArg σ.obj ht.symm)
      have hfac : e.inv ≫ f = P.component σ t := by
        dsimp only [e, f]
        simp
      have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
      rw [← hlinear]
      exact LinearMap.range_comp_le_range e.inv.hom.hom f.hom.hom
    exact
      (le_sup_of_le_right
        (hrange.trans
          (PretorsionImageClosed.range_le_idealRange f.hom.hom hfRad)))
        ⟨_, rfl⟩
  · have hmem : P.label t ∈ C \ {x} := by
      exact ⟨P.mem t, by simpa using ht⟩
    exact le_sup_of_le_left
      (σ.range_le_trace_of_mem hmem (P.component σ t))
      ⟨_, rfl⟩
end PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
