-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sClosure_isClosed_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:59:28.461837+00:00
-- url     : https://prove2.me/submissions/e3e691d7-dfc9-4930-b6fd-abf38b9e4a9a

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty

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
theorem _root_.solution :
    σ.sClosure.IsClosed ∅ := by
  rw [σ.sClosure.isClosed_iff]
  exact sSet_empty σ
end PretorsionImageClosed.IndecomposableSkeleton
