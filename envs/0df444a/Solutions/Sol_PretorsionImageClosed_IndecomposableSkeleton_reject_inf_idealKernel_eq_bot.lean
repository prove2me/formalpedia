-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_inf_idealKernel_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:20:28.092376+00:00
-- url     : https://prove2.me/submissions/a39832a6-9ab3-47dd-87d7-80c0e6f727f1

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_comp_mem_end_jacobson
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_comap_reject
public import Theorems.Thm_PretorsionImageClosed_idealKernel_le_ker


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
    (C : Set ι) {x y : ι} (hxy : x ≠ y)
    (hX :
      σ.reject C (σ.obj x) ⊓
        σ.pointReject y (σ.obj x) = ⊥)
    (hY :
      σ.reject C (σ.obj y) ⊓
        σ.pointReject x (σ.obj y) = ⊥) :
    σ.reject C (σ.obj x) ⊓
        PretorsionImageClosed.idealKernel
          (Ring.jacobson (Module.End R (σ.obj x))) = ⊥ := by
  apply le_antisymm
  · intro z hz
    have hzPoint : z ∈ σ.pointReject y (σ.obj x) := by
      rw [pointReject, Submodule.mem_iInf]
      intro f
      rw [LinearMap.mem_ker]
      have hfReject :
          f.hom.hom z ∈ σ.reject C (σ.obj y) := by
        exact (reject_le_comap_reject σ f) hz.1
      have hfPoint :
          f.hom.hom z ∈ σ.pointReject x (σ.obj y) := by
        rw [pointReject, Submodule.mem_iInf]
        intro g
        rw [LinearMap.mem_ker]
        have hrad :
            g.hom.hom.comp f.hom.hom ∈
              Ring.jacobson
                (Module.End R (σ.obj x)) :=
          comp_mem_end_jacobson σ hxy g f
        have hzero :=
          PretorsionImageClosed.idealKernel_le_ker
            (g.hom.hom.comp f.hom.hom) hrad hz.2
        rw [LinearMap.mem_ker, LinearMap.comp_apply] at hzero
        exact hzero
      have hfbot : f.hom.hom z ∈
          (⊥ : Submodule R (σ.obj y)) := by
        rw [← hY]
        exact ⟨hfReject, hfPoint⟩
      exact hfbot
    rw [← hX]
    exact ⟨hz.1, hzPoint⟩
  · exact bot_le
end PretorsionImageClosed.IndecomposableSkeleton
