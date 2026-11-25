-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:34.155349+00:00
-- url     : https://prove2.me/submissions/84553224-b58c-4c2a-b435-66c948b11d4e

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker
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
theorem _root_.solution {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : X ⟶ σ.obj i) :
    σ.reject S X ≤ LinearMap.ker f.hom.hom := by
  let a : Fin 1 → ι := fun _ ↦ i
  let e :
      σ.sumOver (FintypeCat.of (Fin 1)) a ≅ σ.obj i :=
    biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)
  let g : σ.SelectedMapFrom S X :=
    { index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ hi
      map := f ≫ e.inv }
  have hreject := reject_le_ker σ g
  intro x hx
  have hxcomp := hreject hx
  rw [LinearMap.mem_ker] at hxcomp ⊢
  have hinj : Function.Injective e.inv.hom.hom :=
    (FGModuleCat.mono_iff_injective e.inv).1 inferInstance
  apply hinj
  simpa only [map_zero, g, FGModuleCat.hom_hom_comp,
    LinearMap.comp_apply] using hxcomp
end PretorsionImageClosed.IndecomposableSkeleton
