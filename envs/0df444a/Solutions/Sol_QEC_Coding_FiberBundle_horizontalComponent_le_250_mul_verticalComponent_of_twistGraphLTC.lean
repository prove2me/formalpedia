-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalComponent_le_250_mul_verticalComponent_of_twistGraphLTC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:26.422077+00:00
-- url     : https://prove2.me/submissions/5ebe36bc-71b0-448c-a91f-4cc8125affec

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_twistGraphWordOfHorizontalComponent
import Theorems.Thm_QEC_Coding_FiberBundle_twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
import Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_card_horizontalBoundaryShadow_le_verticalComponent

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
    HammingWeight (horizontalComponent z) ≤
      250 * HammingWeight (verticalComponent z) := by
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
  have hViolVertical :
      TwistGraph.violationCount baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ≤
        HammingWeight (verticalComponent z) :=
    le_trans
      (twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
        baseSample twistSample z)
      (ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
        baseSample twistSample z hz hNormalized)
  exact hSound.trans (Nat.mul_le_mul_left 250 hViolVertical)
end QEC.Coding.FiberBundle
