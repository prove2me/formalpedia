-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.not_mem_qClosure_sdiff_of_isRelativeSplitProjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:35:27.293987+00:00
-- url     : https://prove2.me/submissions/fdc932ab-391e-4232-a1ef-6dca2ad83d98

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
public import Theorems.Thm_PretorsionImageClosed_isLocalRing_end_of_isIndecomposable
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_nonempty_linearEquiv_of_isUnit_comp
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
theorem _root_.solution
    (C : Set ι) (x : ι)
    (hproj : σ.IsRelativeSplitProjective C x) :
    x ∉ σ.qClosure (C \ {x}) := by
  intro hx
  rw [mem_qClosure_iff_inFac] at hx
  obtain ⟨P⟩ := hx
  let PC : σ.FacPresentation C (σ.obj x) :=
    P.of_subset σ (by intro y hy; exact hy.1)
  have hsplit : IsSplitEpi P.map := hproj PC
  letI : IsSplitEpi P.map := hsplit
  letI : Fintype P.index := FintypeCat.fintype
  let comp : P.index → Module.End R (σ.obj x) :=
    fun t ↦
      (P.component σ t).hom.hom.comp
        (CategoryTheory.section_ P.map ≫
          biproduct.π
            (fun t : P.index ↦ σ.obj (P.label t)) t).hom.hom
  have hcat :
      ∑ t : P.index,
          (CategoryTheory.section_ P.map ≫
            biproduct.π
              (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.component σ t =
        𝟙 (σ.obj x) := by
    calc
      (∑ t : P.index,
          (CategoryTheory.section_ P.map ≫
            biproduct.π
              (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.component σ t) =
          CategoryTheory.section_ P.map ≫
            (∑ t : P.index,
              biproduct.π
                (fun t : P.index ↦ σ.obj (P.label t)) t ≫
              biproduct.ι
                (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.map := by
        simp only [FacPresentation.component, Category.assoc,
          Preadditive.comp_sum, Preadditive.sum_comp]
      _ = CategoryTheory.section_ P.map ≫ P.map := by
        rw [biproduct.total]
        simp
      _ = 𝟙 (σ.obj x) := IsSplitEpi.id P.map
  let underlying :
      (σ.obj x ⟶ σ.obj x) →+
        Module.End R (σ.obj x) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum :
      (∑ t : P.index,
          ((CategoryTheory.section_ P.map ≫
            biproduct.π
              (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.component σ t)).hom.hom =
        ∑ t : P.index, comp t := by
    change
      underlying
          (∑ t : P.index,
            (CategoryTheory.section_ P.map ≫
              biproduct.π
                (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
              P.component σ t) =
        ∑ t : P.index,
          underlying
            ((CategoryTheory.section_ P.map ≫
              biproduct.π
                (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
              P.component σ t)
    simpa only [comp, FGModuleCat.hom_hom_comp] using
      map_sum underlying
        (fun t : P.index ↦
          (CategoryTheory.section_ P.map ≫
            biproduct.π
              (fun t : P.index ↦ σ.obj (P.label t)) t) ≫
            P.component σ t)
        Finset.univ
  have hcompSum : (∑ t : P.index, comp t) = 1 := by
    rw [← hsum]
    rw [hcat]
    rfl
  letI : IsLocalRing (Module.End R (σ.obj x)) :=
    PretorsionImageClosed.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength x) (σ.indecomposable x)
  have hunit : IsUnit (∑ t : P.index, comp t) := by
    rw [hcompSum]
    exact isUnit_one
  obtain ⟨t, _, htunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := comp) hunit
  obtain ⟨e⟩ :=
    PretorsionImageClosed.nonempty_linearEquiv_of_isUnit_comp
      (σ.indecomposable x) (σ.indecomposable (P.label t))
      (P.component σ t).hom.hom
      (CategoryTheory.section_ P.map ≫
        biproduct.π
          (fun t : P.index ↦ σ.obj (P.label t)) t).hom.hom
      htunit
  have heq : x = P.label t :=
    σ.eq_of_iso ⟨e.toFGModuleCatIso⟩
  apply (P.mem t).2
  exact Set.mem_singleton_iff.mpr heq.symm
end PretorsionImageClosed.IndecomposableSkeleton
