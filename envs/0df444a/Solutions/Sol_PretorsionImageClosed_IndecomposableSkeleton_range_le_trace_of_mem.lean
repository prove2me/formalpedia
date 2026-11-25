-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.range_le_trace_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:59:16.927144+00:00
-- url     : https://prove2.me/submissions/7498cbf6-23b3-4e23-b411-a15b52fb19ad

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_range_le_trace
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_range_eq_top_of_epi

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
theorem _root_.solution {S : Set ι} {i : ι}
    (hi : i ∈ S) {X : FGModuleCat.{w} R}
    (f : σ.obj i ⟶ X) :
    LinearMap.range f.hom.hom ≤ σ.trace S X := by
  let a : Fin 1 → ι := fun _ ↦ i
  let e :
      σ.sumOver (FintypeCat.of (Fin 1)) a ⟶ σ.obj i :=
    (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom
  let g : σ.SelectedMapTo S X :=
    { index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ hi
      map := e ≫ f }
  have hepi : Epi e := inferInstance
  have herange : LinearMap.range e.hom.hom = ⊤ :=
    FGModuleCat.range_eq_top_of_epi e
  have hcomp :
      LinearMap.range (f.hom.hom.comp e.hom.hom) =
        LinearMap.range f.hom.hom :=
    LinearMap.range_comp_of_range_eq_top f.hom.hom herange
  rw [← hcomp]
  simpa only [g, FGModuleCat.hom_hom_comp] using range_le_trace σ g
end PretorsionImageClosed.IndecomposableSkeleton
