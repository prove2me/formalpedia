-- Prove2me | solution 1 for ZetaZeros.D.EllReg.adjointPairingLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:47.60754+00:00
-- url     : https://prove2.me/submissions/63f223d9-0046-49df-aa01-c8fa9e867299

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingLocal
import Theorems.Thm_ZetaZeros_D_EllReg_dw_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]
end ZetaZeros.D.EllReg
