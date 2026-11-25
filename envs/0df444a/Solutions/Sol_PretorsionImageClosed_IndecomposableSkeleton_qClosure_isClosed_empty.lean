-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qClosure_isClosed_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:37:37.682038+00:00
-- url     : https://prove2.me/submissions/1098fd04-b432-4365-8f40-4af257a96c4b

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty

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
    σ.qClosure.IsClosed ∅ := by
  rw [σ.qClosure.isClosed_iff]
  exact qSet_empty σ
end PretorsionImageClosed.IndecomposableSkeleton
