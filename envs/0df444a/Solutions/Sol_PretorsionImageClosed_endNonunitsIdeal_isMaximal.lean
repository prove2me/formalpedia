-- Prove2me | solution 1 for PretorsionImageClosed.endNonunitsIdeal_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:14:41.936173+00:00
-- url     : https://prove2.me/submissions/ffc9ef28-a838-4942-b6df-dae314797e24

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty


attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
namespace PretorsionImageClosed
theorem _root_.solution
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hXlen : IsFiniteLength A X) :
    (endNonunitsIdeal hX hXlen).IsMaximal := by
  letI : Nontrivial X := hX.nontrivial
  rw [Ideal.isMaximal_iff]
  constructor
  · change ¬ ¬ IsUnit (1 : Module.End A X)
    exact not_not_intro isUnit_one
  · intro J x _ hx hxJ
    have hxunit : IsUnit x := by
      by_contra hxu
      exact hx ((mem_endNonunitsIdeal_iff hX hXlen x).2 hxu)
    have hJtop : J = ⊤ := J.eq_top_of_isUnit_mem hxJ hxunit
    rw [hJtop]
    exact Set.mem_univ 1
end PretorsionImageClosed
