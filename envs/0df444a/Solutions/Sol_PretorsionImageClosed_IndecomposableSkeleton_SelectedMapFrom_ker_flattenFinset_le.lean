-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom.ker_flattenFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:38:06.417387+00:00
-- url     : https://prove2.me/submissions/e4f0d877-a517-4f6b-8201-6efb55422d49

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty

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
open PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom
namespace PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom
theorem _root_.solution
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapFrom S X))
    (f : σ.SelectedMapFrom S X) (hf : f ∈ F) :
    LinearMap.ker (flattenFinset σ F).map.hom.hom ≤
      LinearMap.ker f.map.hom.hom := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapFrom S X :=
    fun t ↦ (F.equivFin.symm t).1
  let t : outer := F.equivFin ⟨f, hf⟩
  have hpick : pick t = f := by
    simp [pick, t]
  rw [← hpick]
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver
          (FintypeCat.of (Σ t : outer, (pick t).index))
          (fun p ↦ (pick p.1).label p.2) :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  let e :
      σ.sumOver
          (flattenFinset σ F).index
          (flattenFinset σ F).label ⟶
        σ.sumOver (pick t).index (pick t).label :=
    flattenIso.inv ≫
      biproduct.π (fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) t
  have hfac :
      (flattenFinset σ F).map ≫ e = (pick t).map := by
    dsimp only [e, flattenFinset]
    change
      (biproduct.lift (fun t : outer ↦ (pick t).map) ≫
        flattenIso.hom) ≫
          (flattenIso.inv ≫
            biproduct.π (fun t : outer ↦
              σ.sumOver (pick t).index (pick t).label) t) =
        (pick t).map
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      biproduct.lift_π]
  have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
  simp only [FGModuleCat.hom_hom_comp] at hlinear
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hlinear]
  simp only [LinearMap.comp_apply, hx, map_zero]
end PretorsionImageClosed.IndecomposableSkeleton.SelectedMapFrom
