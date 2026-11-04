-- Prove2me | solution 1 for ThreeSum.LightExtensionSeedRow.trajectory_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:47.412746+00:00
-- url     : https://prove2.me/submissions/da4fec63-7b31-43b6-92ca-f32867a87084

import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionSeedRow
open Light
set_option maxHeartbeats 2000000
namespace ThreeSum.LightExtensionSeedRow
theorem _root_.solution (mul : ℕ → ℕ → ℕ) {q x y : ℕ}
    (hx : x<q) (hy : y<q) (hm : ∀ a<q, ∀ b<q, mul a b<q) (i : ℕ) :
    trajectory mul x y i<q := by
  induction i with
  | zero => exact hy
  | succ i hi => exact hm _ hi x hx
end ThreeSum.LightExtensionSeedRow
