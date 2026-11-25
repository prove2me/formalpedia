-- Prove2me | solution 1 for PretorsionImageClosed.nonempty_linearEquiv_of_isUnit_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:11:54.39205+00:00
-- url     : https://prove2.me/submissions/33952944-23ff-4e03-ba5a-65f79a621896

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_eq_zero_or_eq_one_of_isIdempotentElem
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_nontrivial
public import Theorems.Thm_PretorsionImageClosed_IsLocalRing_eq_zero_or_eq_one_of_isIdempotentElem
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty



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
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    (hX : PretorsionImageClosed.IsIndecomposableModule A X)
    (hY : PretorsionImageClosed.IsIndecomposableModule A Y)
    (f : Y →ₗ[A] X) (g : X →ₗ[A] Y)
    (hunit : IsUnit (f.comp g)) :
    Nonempty (X ≃ₗ[A] Y) := by
  let e : X ≃ₗ[A] X :=
    { f.comp g,
      Equiv.ofBijective (f.comp g)
        ((Module.End.isUnit_iff _).mp hunit) with }
  let r : Y →ₗ[A] X := e.symm.toLinearMap.comp f
  have hrg : r.comp g = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  let p : Module.End A Y := g.comp r
  have hp : IsIdempotentElem p := by
    change p * p = p
    rw [Module.End.mul_eq_comp]
    ext y
    simp only [p, LinearMap.comp_apply]
    have h := LinearMap.congr_fun hrg (r y)
    simpa using congrArg g h
  rcases hY.eq_zero_or_eq_one_of_isIdempotentElem hp with hp0 | hp1
  · have hg0 : g = 0 := by
      calc
        g = p.comp g := by
          ext x
          simp only [p, LinearMap.comp_apply]
          have h := LinearMap.congr_fun hrg x
          simpa using congrArg g h.symm
        _ = 0 := by rw [hp0, LinearMap.zero_comp]
    have hzero : (f.comp g : Module.End A X) = 0 := by
      simp [hg0]
    rw [hzero] at hunit
    letI := hX.nontrivial
    exact (not_isUnit_zero hunit).elim
  · exact ⟨
      { toLinearMap := g
        invFun := r
        left_inv := fun x => LinearMap.congr_fun hrg x
        right_inv := fun y => by
          have h := LinearMap.congr_fun hp1 y
          simpa [p, Module.End.one_apply] using h }⟩
end PretorsionImageClosed
