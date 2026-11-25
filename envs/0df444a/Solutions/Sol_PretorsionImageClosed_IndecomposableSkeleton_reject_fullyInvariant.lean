-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:14:15.647424+00:00
-- url     : https://prove2.me/submissions/3d3aca2a-9822-4b33-a370-39850d102e82

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_comap_reject

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
    (X : FGModuleCat.{w} R) (f : X ⟶ X) :
    σ.reject S X ≤ Submodule.comap f.hom.hom (σ.reject S X) :=
  reject_le_comap_reject σ f
end PretorsionImageClosed.IndecomposableSkeleton
