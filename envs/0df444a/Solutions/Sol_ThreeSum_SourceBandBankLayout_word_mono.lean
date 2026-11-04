-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:45.408596+00:00
-- url     : https://prove2.me/submissions/9d42d3d0-398f-4795-826a-e0f3ebfffb00

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightBlockSourceRetainedHost.word NL NR h J ≤ LightBlockSourceRetainedHost.word NL' NR' h J := by
  have hpl := Nat.mul_le_mul_left (2^(J*(512*h))) hl
  have hpr := Nat.mul_le_mul_left (2^(J*(512*h))) hr
  unfold LightBlockSourceRetainedHost.word LightSourceRetainedStages.word
  omega
end ThreeSum.SourceBandBankLayout
