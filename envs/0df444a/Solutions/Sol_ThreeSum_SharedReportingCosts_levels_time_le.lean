-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.levels_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:08:46.739536+00:00
-- url     : https://prove2.me/submissions/e933b131-1b73-4883-8137-d46c243d96d2

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Definitions.Def_WeightedCache3SUM_Alias_418e05005a34b027
import Theorems.Thm_ThreeSum_SharedReportingCosts_terminal_le_blocks

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n : ℕ) : levelsTime n ≤ overhead n*allPrefixBoxes n := by
  unfold levelsTime allPrefixBoxes
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply time_le_boxes
  exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (terminal_le_blocks n)
end ThreeSum.SharedReportingCosts
