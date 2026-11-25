-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:03:41.233052+00:00
-- url     : https://prove2.me/submissions/6dbac718-f215-4c5d-9a2a-be411ee6ef82

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces

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
theorem _root_.solution {S T : Set ι} (hST : S ⊆ T)
    (X : FGModuleCat.{w} R) :
    σ.reject T X ≤ σ.reject S X := by
  apply le_iInf
  intro f
  let g : σ.SelectedMapFrom T X :=
    { index := f.index
      label := f.label
      mem := fun t ↦ hST (f.mem t)
      map := f.map }
  exact iInf_le_of_le g le_rfl
end PretorsionImageClosed.IndecomposableSkeleton
