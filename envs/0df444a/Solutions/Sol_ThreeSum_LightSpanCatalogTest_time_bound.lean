-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogTest.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:25.322767+00:00
-- url     : https://prove2.me/submissions/6683e190-23f9-43de-8493-f595ab274abc

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSpanCatalogTest
theorem _root_.solution (J n : ℕ) : time J n≤300*(n+1)*(J+1) := by
  unfold time LightSpanRowEqual.time
  nlinarith
end ThreeSum.LightSpanCatalogTest
