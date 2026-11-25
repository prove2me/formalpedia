-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:14:19.393831+00:00
-- url     : https://prove2.me/submissions/2ae0aeab-5f82-4a0d-a140-5040a2c5e3b1

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_mono
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_range_le_trace_of_mem
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum_apply

attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub

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
theorem _root_.solution (S T : Set ι) (X : FGModuleCat.{w} R) :
    σ.trace (S ∪ T) X = σ.trace S X ⊔ σ.trace T X := by
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
    let ft : σ.obj (f.label t) ⟶ X :=
      biproduct.ι (fun t : f.index ↦ σ.obj (f.label t)) t ≫ f.map
    have hmemRange :
        ft
          ((biproduct.π
            (fun t : f.index ↦ σ.obj (f.label t)) t) y) ∈
          LinearMap.range ft.hom.hom :=
      LinearMap.mem_range_self ft.hom.hom _
    rcases f.mem t with ht | ht
    · exact
        (show σ.trace S X ≤ σ.trace S X ⊔ σ.trace T X from le_sup_left)
          ((range_le_trace_of_mem σ ht ft) hmemRange)
    · exact
        (show σ.trace T X ≤ σ.trace S X ⊔ σ.trace T X from le_sup_right)
          ((range_le_trace_of_mem σ ht ft) hmemRange)
  · exact sup_le
      (trace_mono σ Set.subset_union_left X)
      (trace_mono σ Set.subset_union_right X)
end PretorsionImageClosed.IndecomposableSkeleton
