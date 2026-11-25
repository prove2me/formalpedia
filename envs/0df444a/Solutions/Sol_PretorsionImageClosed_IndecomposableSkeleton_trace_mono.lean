-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:58:49.591251+00:00
-- url     : https://prove2.me/submissions/310e0968-869e-49af-a65f-b720f7532074

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
    σ.trace S X ≤ σ.trace T X := by
  apply iSup_le
  intro f
  let g : σ.SelectedMapTo T X :=
    { index := f.index
      label := f.label
      mem := fun t ↦ hST (f.mem t)
      map := f.map }
  exact le_iSup_of_le g le_rfl
end PretorsionImageClosed.IndecomposableSkeleton
