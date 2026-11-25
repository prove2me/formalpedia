-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:30:26.732664+00:00
-- url     : https://prove2.me/submissions/4e504d3c-f71c-44e7-bc3c-705463efa423

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker_of_mem
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum_apply
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_anti
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
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
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (S T : Set ι) (X : FGModuleCat.{w} R) :
    σ.reject (S ∪ T) X = σ.reject S X ⊓ σ.reject T X := by
  apply le_antisymm
  · exact le_inf
      (reject_anti σ Set.subset_union_left X)
      (reject_anti σ Set.subset_union_right X)
  · apply le_iInf
    intro f
    letI : Fintype f.index := FintypeCat.fintype
    intro x hx
    rw [LinearMap.mem_ker]
    have hmap :
        f.map =
          ∑ t : f.index,
            (f.map ≫
              biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t) ≫
              biproduct.ι
                (fun t : f.index ↦ σ.obj (f.label t)) t := by
      calc
        f.map = f.map ≫ 𝟙 _ := (Category.comp_id _).symm
        _ =
            f.map ≫
              (∑ t : f.index,
                biproduct.π
                    (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                  biproduct.ι
                    (fun t : f.index ↦ σ.obj (f.label t)) t) := by
              rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.comp_sum]
          simp only [Category.assoc]
    rw [hmap, FGModuleCat.hom_hom_sum_apply]
    apply Finset.sum_eq_zero
    intro t _
    let ft : X ⟶ σ.obj (f.label t) :=
      f.map ≫
        biproduct.π (fun t : f.index ↦ σ.obj (f.label t)) t
    have hft : ft.hom.hom x = 0 := by
      rcases f.mem t with ht | ht
      · exact LinearMap.mem_ker.mp
          ((reject_le_ker_of_mem σ ht ft) hx.1)
      · exact LinearMap.mem_ker.mp
          ((reject_le_ker_of_mem σ ht ft) hx.2)
    change
      ((ft ≫
        biproduct.ι
          (fun t : f.index ↦ σ.obj (f.label t)) t).hom.hom) x = 0
    simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply,
      hft, map_zero]
end PretorsionImageClosed.IndecomposableSkeleton
