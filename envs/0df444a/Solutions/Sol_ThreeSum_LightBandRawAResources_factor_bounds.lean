-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:33:18.884993+00:00
-- url     : https://prove2.me/submissions/5c3b8ceb-c106-4364-809c-596966e39094

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (n : ℕ) :
    1 ≤ base n ∧ n+1 ≤ base n ∧ n^2 ≤ base n ∧
      SharedReportingBankResourceBounds.magnitude n ≤ base n ∧
      SharedReportingBankResourceBounds.magnitude n*n^2 ≤ base n := by
  have hq : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hbase : (n+1)^2 ≤ base n := Nat.le_mul_of_pos_left _ (by omega)
  have hn : n+1 ≤ (n+1)^2 := Nat.le_self_pow (by decide) _
  refine ⟨hq.trans hbase,hn.trans hbase,
    (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans hbase,?_,?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hq)
  · exact Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_left (Nat.le_succ _) 2)
end ThreeSum.LightBandRawAResources
