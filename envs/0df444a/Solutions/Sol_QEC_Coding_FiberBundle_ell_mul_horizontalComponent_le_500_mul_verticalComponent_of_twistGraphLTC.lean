-- Prove2me | solution 1 for QEC.Coding.FiberBundle.ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:52.499193+00:00
-- url     : https://prove2.me/submissions/ed833fee-60a8-4a03-8a9e-3e4a0e63b09e

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraphWordOfHorizontalComponent
import Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z) ≤
        ell * (4 * r)) :
    ell * HammingWeight (horizontalComponent z) ≤
      500 * HammingWeight (verticalComponent z) := by
  have hSmallTwist :
      5000 * Delta *
          HammingWeight (twistGraphWordOfHorizontalComponent z) ≤
        ell * (4 * r) := by
    rw [hammingWeight_twistGraphWordOfHorizontalComponent
      z hNormalized]
    exact hSmall
  have hSound :=
    hLTC (twistGraphWordOfHorizontalComponent z) hSmallTwist
  rw [hammingWeight_twistGraphWordOfHorizontalComponent
    z hNormalized] at hSound
  have hStrings :=
    ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
      baseSample twistSample z hz hNormalized
  calc
    ell * HammingWeight (horizontalComponent z) ≤
        ell * (250 *
          TwistGraph.violationCount baseSample twistSample
            (twistGraphWordOfHorizontalComponent z)) :=
      Nat.mul_le_mul_left ell hSound
    _ = 250 * (ell *
          TwistGraph.violationCount baseSample twistSample
            (twistGraphWordOfHorizontalComponent z)) := by ac_rfl
    _ ≤ 250 * (2 * HammingWeight (verticalComponent z)) :=
      Nat.mul_le_mul_left 250 hStrings
    _ = 500 * HammingWeight (verticalComponent z) := by ring
end QEC.Coding.FiberBundle
