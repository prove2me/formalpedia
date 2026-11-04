-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.host_space_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:20.77122+00:00
-- url     : https://prove2.me/submissions/322692dc-3b13-4eda-8c95-c46a48606326

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution (base free h J : ℕ) :
    LightBlockSourceRetainedHost.space (base+free) h J=
      base+LightBlockSourceRetainedHost.space free h J := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
  omega
end ThreeSum.SourceBandBankLayout
