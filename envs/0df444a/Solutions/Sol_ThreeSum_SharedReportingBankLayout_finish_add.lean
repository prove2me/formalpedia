-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.finish_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:22.45778+00:00
-- url     : https://prove2.me/submissions/0d4c86d3-07c6-4928-a971-94401c5b1533

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution (base h J k boxCut : ℕ) :
    finish base h J k boxCut=base+cellSize h J k boxCut := by
  unfold cellSize finish work masks boxes pointers stageR stageL pairR pairL
  omega
end ThreeSum.SharedReportingBankLayout
