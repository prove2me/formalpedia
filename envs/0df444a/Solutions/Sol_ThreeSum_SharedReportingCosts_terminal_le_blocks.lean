-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.terminal_le_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:25.532752+00:00
-- url     : https://prove2.me/submissions/5d1e0302-b7be-4ce9-b4d1-fd1edf6e8205

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n : ℕ) : Switch.terminalDepth n ≤ blocks n := by
  have hh := Switch.actual_depth_condition (n := n) (le_refl (Switch.terminalDepth n))
  change 20*Switch.terminalDepth n ≤ 13*blocks n at hh
  omega
end ThreeSum.SharedReportingCosts
