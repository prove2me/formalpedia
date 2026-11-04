-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.slot_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:00.121527+00:00
-- url     : https://prove2.me/submissions/80a9c53b-eb21-4f0d-8d88-796c482a7727

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution (base count W cut : ℕ) : Monotone (slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _
end ThreeSum.LightBlockSourceBatchLayout
