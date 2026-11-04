-- Prove2me | solution 1 for ThreeSum.LightSpanRowEqual.flag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:39.704735+00:00
-- url     : https://prove2.me/submissions/f3d8d2b0-0d1f-427a-975c-a2a6688770af

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanRowEqual
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
namespace ThreeSum.LightSpanRowEqual
theorem _root_.solution (f g : ℕ → ℤ) (j : ℕ) : flag f g j≤1 := by unfold flag; split <;> omega
end ThreeSum.LightSpanRowEqual
