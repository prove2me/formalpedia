-- Prove2me | solution 1 for QEC.Coding.FiberBundle.ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:36.556693+00:00
-- url     : https://prove2.me/submissions/5d923a8e-5057-41bf-83b1-aef739dd82de

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_cycleBoundary_eq_coarseBoundaryWord
import Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_violationCount_eq_sum_checkColumn
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_verticalComponent_eq_sum_fibers


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
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z) :
    ell *
        TwistGraph.violationCount baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ≤
      2 * HammingWeight (verticalComponent z) := by
  rw [TwistGraph.violationCount_eq_sum_checkColumn,
    hammingWeight_verticalComponent_eq_sum_fibers,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  rw [hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
    baseSample twistSample z hz a]
  have hSupport :
      ∀ j,
        cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j ≠ 0 →
          fiberResidue ell j = 0 := by
    intro j hj
    apply fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
      baseSample twistSample z hNormalized a j
    rw [horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
      baseSample twistSample z hz a]
    exact hj
  rw [← hammingWeight_cycleBoundary_eq_coarseBoundaryWord
    ell (verticalFiber z a) hSupport]
  exact ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
    ell (verticalFiber z a) hSupport
end QEC.Coding.FiberBundle
