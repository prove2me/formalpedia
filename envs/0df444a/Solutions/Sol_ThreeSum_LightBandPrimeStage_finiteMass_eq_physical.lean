-- Prove2me | solution 1 for ThreeSum.LightBandPrimeStage.finiteMass_eq_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:12:00.843506+00:00
-- url     : https://prove2.me/submissions/a5058189-d268-4927-9ae1-a29ad5278035

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Theorems.Thm_ThreeSum_BandPrimeScales_physicalMass_eq_score
import Theorems.Thm_ThreeSum_BandRawA_finiteAll_weightedFalseCount


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeStage
theorem _root_.solution (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    finiteMass n q nA nB nC A B C rs=BandPrimeScales.physicalMass n q nA nB nC A B C rs := by
  rw [BandPrimeScales.physicalMass_eq_score]
  exact BandRawA.finiteAll_weightedFalseCount _ _ _ _ _ _ _ _ _ _ _
end ThreeSum.LightBandPrimeStage
