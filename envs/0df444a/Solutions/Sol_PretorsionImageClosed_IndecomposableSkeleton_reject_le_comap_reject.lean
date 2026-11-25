-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_le_comap_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:00:48.017164+00:00
-- url     : https://prove2.me/submissions/f0311cf3-be2f-4b54-9eb4-c669e3372624

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
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
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
theorem _root_.solution {S : Set ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S Y) := by
  change
    (⨅ h : σ.SelectedMapFrom S X,
      LinearMap.ker h.map.hom.hom) ≤
        Submodule.comap f.hom.hom
          (⨅ g : σ.SelectedMapFrom S Y,
            LinearMap.ker g.map.hom.hom)
  rw [Submodule.comap_iInf]
  apply le_iInf
  intro g
  let h : σ.SelectedMapFrom S X :=
    { index := g.index
      label := g.label
      mem := g.mem
      map := f ≫ g.map }
  have hker :
      (⨅ k : σ.SelectedMapFrom S X,
        LinearMap.ker k.map.hom.hom) ≤
          LinearMap.ker h.map.hom.hom :=
    iInf_le (fun k : σ.SelectedMapFrom S X ↦
      LinearMap.ker k.map.hom.hom) h
  simpa only [h, FGModuleCat.hom_hom_comp, LinearMap.ker_comp] using hker
end PretorsionImageClosed.IndecomposableSkeleton
