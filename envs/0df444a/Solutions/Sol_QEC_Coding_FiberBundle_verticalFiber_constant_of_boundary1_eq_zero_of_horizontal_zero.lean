-- Prove2me | solution 1 for QEC.Coding.FiberBundle.verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:46.221824+00:00
-- url     : https://prove2.me/submissions/e8d8adcb-fa29-4d25-ac25-e66132b443c4

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_boundary1_apply_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberChainBoundary_eq_zero_implies_constant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzCycle :
      boundary1
        (RandomTwist.fiberBundleData baseSample twistSample) z = 0)
    (hzHorizontal : ∀ b : Fin (4 * r), horizontalFiber z b = 0)
    (a : Fin (3 * r)) :
    ∀ j, verticalFiber z a j = verticalFiber z a 0 := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  apply cycleFiberChainBoundary_eq_zero_implies_constant
    (ell * ell) (by nlinarith)
  funext i
  have hi := congrFun hzCycle (a, i)
  rw [boundary1_apply_eq_horizontal_add_vertical] at hi
  have hHorizontalSum :
      (∑ b : Fin (4 * r),
        (RandomTwist.fiberBundleData baseSample twistSample).baseBoundary a b *
          z (Sum.inl (b,
            ((RandomTwist.fiberBundleData baseSample twistSample
              ).connection b a).onZero.symm i))) = 0 := by
    apply Finset.sum_eq_zero
    intro b _hb
    have hb := congrFun (hzHorizontal b)
      ((((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero.symm) i)
    change z (Sum.inl (b,
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero.symm i)) = 0 at hb
    rw [hb, mul_zero]
  rw [hHorizontalSum, zero_add] at hi
  change cycleFiberChainBoundary (ell * ell) (verticalFiber z a) i = 0
  exact hi
end QEC.Coding.FiberBundle
