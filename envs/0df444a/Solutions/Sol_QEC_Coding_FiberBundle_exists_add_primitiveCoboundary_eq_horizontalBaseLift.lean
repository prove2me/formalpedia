-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_add_primitiveCoboundary_eq_horizontalBaseLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:17.46888+00:00
-- url     : https://prove2.me/submissions/f9252116-ab26-4f1f-90dd-dc588dcbe25d

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCocoboundary_apply_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
import Theorems.Thm_QEC_Coding_FiberBundle_verticalComponent_add_primitiveCoboundary_eq_zero
import Theorems.Thm_QEC_Coding_FiberBundle_add_bundleCoboundary_mem_middleCocycleCode_iff
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_eq_zero_implies_constant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z) =
        horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let u := verticalFiberPrimitiveWord z
  let cleared := z + bundleCoboundary D u
  have hzCleared :
      cleared ∈ (chainComplex D).middleCocycleCode.carrier := by
    exact
      (add_bundleCoboundary_mem_middleCocycleCode_iff D z u).mpr hz
  have hCocycleZero : bundleCocoboundary D cleared = 0 :=
    (mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero D cleared).mp
      hzCleared
  have hVertical : verticalComponent cleared = 0 := by
    exact verticalComponent_add_primitiveCoboundary_eq_zero
      baseSample twistSample hRank z hz
  let x : Word (ZMod 2) (Fin (4 * r)) :=
    fun b => horizontalFiber cleared b 0
  refine ⟨x, ?_⟩
  funext q
  rcases q with ⟨bi⟩ | ⟨aj⟩
  · rcases bi with ⟨b, i⟩
    have hHorizontalCoboundary :
        cycleFiberCoboundary (ell * ell)
          (horizontalFiber cleared b) = 0 := by
      funext j
      have hj := congrFun hCocycleZero (b, j)
      rw [bundleCocoboundary_apply_eq_horizontal_add_vertical] at hj
      have hVerticalSum :
          (∑ a : Fin (3 * r),
            cleared (Sum.inr (a, (D.connection b a).onOne j)) *
              D.baseBoundary a b) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha := congrFun hVertical
          (a, (D.connection b a).onOne j)
        change cleared
          (Sum.inr (a, (D.connection b a).onOne j)) = 0 at ha
        rw [ha, zero_mul]
      rw [hVerticalSum, add_zero] at hj
      exact hj
    have hEll : 2 ≤ ell := by
      have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
      omega
    have hCycle : 2 ≤ ell * ell := by nlinarith
    have hConstant :=
      cycleFiberCoboundary_eq_zero_implies_constant
        (ell * ell) hCycle (horizontalFiber cleared b)
        hHorizontalCoboundary i
    exact hConstant
  · rcases aj with ⟨a, j⟩
    have haj := congrFun hVertical (a, j)
    exact haj
end QEC.Coding.FiberBundle
