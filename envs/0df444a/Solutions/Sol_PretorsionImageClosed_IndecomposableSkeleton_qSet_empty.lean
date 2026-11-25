-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:30:13.262825+00:00
-- url     : https://prove2.me/submissions/e04a2591-a3b1-4ed5-9c31-1a9f63693d17

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qSet_iff_trace_eq_top
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial

attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty

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
theorem _root_.solution : σ.qSet ∅ = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have htrace :=
    (mem_qSet_iff_trace_eq_top σ ∅ j).1 hj
  rw [trace_empty] at htrace
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  exact bot_ne_top htrace
end PretorsionImageClosed.IndecomposableSkeleton
