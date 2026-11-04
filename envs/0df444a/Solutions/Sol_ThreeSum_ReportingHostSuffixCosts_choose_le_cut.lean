-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixCosts.choose_le_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:03.208146+00:00
-- url     : https://prove2.me/submissions/843a6044-c08b-407b-9eba-50aa34ca88c8

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffixCosts
theorem _root_.solution {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
end ThreeSum.ReportingHostSuffixCosts
