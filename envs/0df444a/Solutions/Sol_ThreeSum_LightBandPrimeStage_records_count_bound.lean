-- Prove2me | solution 1 for ThreeSum.LightBandPrimeStage.records_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:40.470102+00:00
-- url     : https://prove2.me/submissions/413e676c-fe8a-4a1e-93cf-39d7706dcb46

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Theorems.Thm_ThreeSum_BandCandidateRows_count_bound
import Theorems.Thm_ThreeSum_BandRawA_count_bound
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeStage
theorem _root_.solution {A B C : Family} {n nA nB nC : ℕ}
    (hA : A.size=BandPartition.size nA (bandSize n))
    (hB : B.size=BandPartition.size nB (bandSize n))
    (hC : C.size=BandPartition.size nC (bandSize n))
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    (records A B C).length ≤ 3*bandCount n^2 :=
  count_bound (hA.le.trans (SourceBandCosts.size_le_bandCount ha))
    (hB.le.trans (SourceBandCosts.size_le_bandCount hb))
    (hC.le.trans (SourceBandCosts.size_le_bandCount hc))
end ThreeSum.LightBandPrimeStage
