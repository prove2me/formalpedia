-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixBoxes.residual_le_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:43.079194+00:00
-- url     : https://prove2.me/submissions/5cc10bc4-1c67-4c6b-91db-13292f36ef74

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixBoxes
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix
variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingSuffixBoxes
theorem _root_.solution {h J k : ℕ} : residualSize h J k ≤ suffixStage J (512*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)
end ThreeSum.LightReportingSuffixBoxes
