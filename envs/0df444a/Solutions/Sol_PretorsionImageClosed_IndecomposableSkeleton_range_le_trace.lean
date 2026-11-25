-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.range_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:45.395308+00:00
-- url     : https://prove2.me/submissions/61a611f7-6a6b-4f79-a2e1-4e066b4e80c8

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
theorem _root_.solution {S : Set ι} {X : FGModuleCat.{w} R}
    (f : σ.SelectedMapTo S X) :
    LinearMap.range f.map.hom.hom ≤ σ.trace S X :=
  le_iSup (fun g : σ.SelectedMapTo S X ↦
    LinearMap.range g.map.hom.hom) f
end PretorsionImageClosed.IndecomposableSkeleton
