-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:51.308025+00:00
-- url     : https://prove2.me/submissions/85875452-9c01-41aa-ad74-82a8a80d408e

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
    (f : σ.SelectedMapFrom S X) :
    σ.reject S X ≤ LinearMap.ker f.map.hom.hom :=
  iInf_le (fun g : σ.SelectedMapFrom S X ↦
    LinearMap.ker g.map.hom.hom) f
end PretorsionImageClosed.IndecomposableSkeleton
