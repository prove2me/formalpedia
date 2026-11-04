-- Prove2me | solution 1 for ThreeSum.LightBandPrimeStage.records_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:51.529285+00:00
-- url     : https://prove2.me/submissions/d2a8b686-1d71-4692-8d1f-ff359adde7d9

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Theorems.Thm_ThreeSum_BandCandidateRows_records_sound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeStage
theorem _root_.solution {A B C : Family} {nA nB nC g : ℕ}
    (hA : A.size=BandPartition.size nA g)
    (hB : B.size=BandPartition.size nB g)
    (hC : C.size=BandPartition.size nC g) (hg : 0 < g) :
    ∀ r ∈ records A B C, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC := by
  intro r hr hf
  obtain ⟨ha,hb,hc,_⟩ := records_sound hr hf
  rw [hA] at ha
  rw [hB] at hb
  rw [hC] at hc
  exact ⟨(BandPartition.start_lt hg ha).le,(BandPartition.start_lt hg hb).le,
    (BandPartition.start_lt hg hc).le⟩
end ThreeSum.LightBandPrimeStage
