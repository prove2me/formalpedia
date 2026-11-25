-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.mem_sSet_iff_reject_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:22.908958+00:00
-- url     : https://prove2.me/submissions/035a0308-9b91-48cf-9921-3b94f1e2b290

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inSub_iff_reject_eq_bot

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
theorem _root_.solution (S : Set ι) (j : ι) :
    j ∈ σ.sSet S ↔ σ.reject S (σ.obj j) = ⊥ :=
  inSub_iff_reject_eq_bot σ S (σ.obj j) (σ.finiteLength j)
end PretorsionImageClosed.IndecomposableSkeleton
