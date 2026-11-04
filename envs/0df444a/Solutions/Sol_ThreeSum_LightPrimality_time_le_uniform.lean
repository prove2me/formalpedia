-- Prove2me | solution 1 for ThreeSum.LightPrimality.time_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:32:04.8905+00:00
-- url     : https://prove2.me/submissions/b15d2a97-775b-4c5d-a269-76492acb3de2

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimality
theorem _root_.solution {n maxValue : ℕ} (hn : n ≤ maxValue) :
    time n maxValue ≤ time maxValue maxValue := by
  unfold time
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hn 2)) _
end ThreeSum.LightPrimality
