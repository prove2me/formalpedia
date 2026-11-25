-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_singleton_eq_pointTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:39.496481+00:00
-- url     : https://prove2.me/submissions/8690ab00-a70d-4ac5-93db-a13ee996e96c

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum_apply
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
theorem _root_.solution (i : ι)
    (X : FGModuleCat.{w} R) :
    σ.trace {i} X = σ.pointTrace i X := by
  apply le_antisymm
  · apply iSup_le
    intro f
    letI : Fintype f.index := FintypeCat.fintype
    rintro x ⟨y, rfl⟩
    have hmap :
        f.map =
          ∑ t : f.index,
            biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t ≫
              (biproduct.ι
                  (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                f.map) := by
      calc
        f.map = 𝟙 _ ≫ f.map := (Category.id_comp _).symm
        _ =
            (∑ t : f.index,
              biproduct.π
                  (fun t : f.index ↦ σ.obj (f.label t)) t ≫
                biproduct.ι
                  (fun t : f.index ↦ σ.obj (f.label t)) t) ≫
              f.map := by rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
    rw [hmap, FGModuleCat.hom_hom_sum_apply]
    apply Submodule.sum_mem
    intro t _
    have ht : f.label t = i := by
      simpa using f.mem t
    let ft : σ.obj (f.label t) ⟶ X :=
      biproduct.ι (fun t : f.index ↦ σ.obj (f.label t)) t ≫ f.map
    let ft' : σ.obj i ⟶ X :=
      eqToHom (congrArg σ.obj ht.symm) ≫ ft
    have hcat :
        eqToHom (congrArg σ.obj ht) ≫ ft' = ft := by
      dsimp only [ft']
      simp
    have hvalue :
        ft
            ((biproduct.π
              (fun t : f.index ↦ σ.obj (f.label t)) t) y) =
          ft'
            ((eqToHom (congrArg σ.obj ht))
              ((biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t) y)) := by
      exact
        (congrArg
          (fun q : σ.obj (f.label t) ⟶ X ↦
            q
              ((biproduct.π
                (fun t : f.index ↦ σ.obj (f.label t)) t) y))
          hcat).symm
    change
      ft
          ((biproduct.π
            (fun t : f.index ↦ σ.obj (f.label t)) t) y) ∈
        σ.pointTrace i X
    rw [hvalue]
    exact le_iSup
      (fun g : σ.obj i ⟶ X ↦ LinearMap.range g.hom.hom) ft'
      (LinearMap.mem_range_self ft'.hom.hom _)
  · apply iSup_le
    intro f
    exact range_le_trace_of_mem σ (Set.mem_singleton i) f
end PretorsionImageClosed.IndecomposableSkeleton
