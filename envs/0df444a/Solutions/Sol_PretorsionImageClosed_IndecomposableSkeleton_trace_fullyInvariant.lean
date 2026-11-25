-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:14:14.53875+00:00
-- url     : https://prove2.me/submissions/d9dc0845-b4ca-4f44-9a68-23df5985a14d

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_map_trace_le_trace

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
    Submodule.map f.hom.hom (σ.trace S X) ≤ σ.trace S X :=
  map_trace_le_trace σ f
end PretorsionImageClosed.IndecomposableSkeleton
