-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogTest.flag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:15.764518+00:00
-- url     : https://prove2.me/submissions/6a19a948-7c55-4eaf-a8f8-6c1f52255ccf

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
namespace ThreeSum.LightSpanCatalogTest
theorem _root_.solution (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : flag f row J n≤1 := by
  unfold flag; split <;> omega
end ThreeSum.LightSpanCatalogTest
