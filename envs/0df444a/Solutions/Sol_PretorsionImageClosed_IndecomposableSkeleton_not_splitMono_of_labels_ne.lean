-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_splitMono_of_labels_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:38.354403+00:00
-- url     : https://prove2.me/submissions/949a3a6e-ea67-4da1-8d2b-429fab54782e

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_comp_mem_end_jacobson
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_mem_end_jacobson_iff_not_isUnit
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
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (hne : ∀ t, x ≠ P.label t) :
    ¬ Nonempty (SplitMono P.map) := by
  classical
  rintro ⟨s⟩
  letI : Fintype P.index := FintypeCat.fintype
  let a (t : P.index) : σ.obj x ⟶ σ.obj (P.label t) :=
    P.map ≫
      biproduct.π
        (fun j : P.index ↦ σ.obj (P.label j)) t
  let b (t : P.index) : σ.obj (P.label t) ⟶ σ.obj x :=
    biproduct.ι
        (fun j : P.index ↦ σ.obj (P.label j)) t ≫
      s.retraction
  have hcat :
      (𝟙 (σ.obj x)) =
        ∑ t : P.index, a t ≫ b t := by
    rw [← s.id]
    calc
      P.map ≫ s.retraction =
          (P.map ≫ 𝟙 _) ≫ s.retraction := by simp
      _ =
          (P.map ≫
            (∑ t : P.index,
              biproduct.π
                  (fun j : P.index ↦ σ.obj (P.label j)) t ≫
                biproduct.ι
                  (fun j : P.index ↦ σ.obj (P.label j)) t)) ≫
            s.retraction := by rw [biproduct.total]
      _ = ∑ t : P.index, a t ≫ b t := by
        rw [Preadditive.comp_sum, Preadditive.sum_comp]
        simp only [a, b, Category.assoc]
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcat
  simp only [FGModuleCat.hom_hom_id, FGModuleCat.hom_hom_sum,
    FGModuleCat.hom_hom_comp] at hlinear
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hsum :
      (∑ t : P.index,
        (b t).hom.hom.comp (a t).hom.hom) ∈ J := by
    apply Ideal.sum_mem
    intro t _
    exact comp_mem_end_jacobson σ (hne t) (b t) (a t)
  have hone : (1 : Module.End R (σ.obj x)) ∈ J := by
    rw [Module.End.one_eq_id, hlinear]
    exact hsum
  have hnonunit :
      ¬ IsUnit (1 : Module.End R (σ.obj x)) :=
    (PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x) 1).1 hone
  exact hnonunit isUnit_one
end PretorsionImageClosed.IndecomposableSkeleton
