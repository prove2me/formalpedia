-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.map_apply_eq_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:40.093+00:00
-- url     : https://prove2.me/submissions/67449223-2ee0-481d-9496-cb2dbc854871

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
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
    {S : Set ι} {X : FGModuleCat.{w} R}
    (P : σ.FacPresentation S X)
    [Fintype P.index]
    (z : σ.sumOver P.index P.label) :
    P.map.hom.hom z =
      ∑ t : P.index,
        (P.component σ t).hom.hom
          ((biproduct.π
            (fun t : P.index ↦ σ.obj (P.label t)) t).hom.hom z) := by
  have hcat :
      P.map =
        ∑ t : P.index,
          biproduct.π (fun t : P.index ↦ σ.obj (P.label t)) t ≫
            P.component σ t := by
    calc
      P.map = 𝟙 _ ≫ P.map := (Category.id_comp _).symm
      _ =
          (∑ t : P.index,
            biproduct.π (fun t : P.index ↦ σ.obj (P.label t)) t ≫
              biproduct.ι (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.map := by rw [biproduct.total]
      _ =
          ∑ t : P.index,
            biproduct.π (fun t : P.index ↦ σ.obj (P.label t)) t ≫
              P.component σ t := by
        simp only [Preadditive.sum_comp, component, Category.assoc]
  let q : P.index → (σ.sumOver P.index P.label ⟶ X) :=
    fun t ↦
      biproduct.π (fun t : P.index ↦ σ.obj (P.label t)) t ≫
        P.component σ t
  let underlying :
      (σ.sumOver P.index P.label ⟶ X) →+
        (σ.sumOver P.index P.label →ₗ[R] X) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hmodule :
      (∑ t : P.index, q t).hom.hom =
        ∑ t : P.index, (q t).hom.hom := by
    change underlying (∑ t : P.index, q t) =
      ∑ t : P.index, underlying (q t)
    exact map_sum underlying q Finset.univ
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcat
  change P.map.hom.hom = (∑ t : P.index, q t).hom.hom at hlinear
  rw [hmodule] at hlinear
  have happ := LinearMap.congr_fun hlinear z
  let eval :
      (σ.sumOver P.index P.label →ₗ[R] X) →+ X :=
    { toFun := fun f ↦ f z
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have heval :
      (∑ t : P.index, (q t).hom.hom) z =
        ∑ t : P.index, (q t).hom.hom z := by
    change eval (∑ t : P.index, (q t).hom.hom) =
      ∑ t : P.index, eval ((q t).hom.hom)
    exact map_sum eval (fun t : P.index ↦ (q t).hom.hom) Finset.univ
  rw [heval] at happ
  simpa only [q, FGModuleCat.hom_hom_comp, LinearMap.comp_apply] using happ
end PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
