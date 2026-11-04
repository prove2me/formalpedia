-- Prove2me | solution 1 for ThreeSum.WeightedModuli.joint_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:00.224421+00:00
-- url     : https://prove2.me/submissions/aa43f8e7-988e-4982-91fa-f4c0025f7d61

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution {q p : ℕ} (hq : 0 < q) (hp : Nat.Prime p) :
    0 < joint q p := by
  unfold joint
  split
  · exact hq
  · exact Nat.mul_pos hq hp.pos
end ThreeSum.WeightedModuli
