-- Prove2me | solution 1 for ThreeSum.Parameters.switch_entropy_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:42.25125+00:00
-- url     : https://prove2.me/submissions/2fd002f1-853d-45c3-bd80-8405c61254d2

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Definitions.Def_WeightedCache3SUM_Alias_94829d9e11dc3ee4

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1 / 2))
    (hmu : 0 < mu)
    (hswitch : phi t < switchThreshold a + 9 / ((1 - a) * mu)) :
    (1 - a) * entropy t <
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hr : 0 < entropyRatio := by norm_num [entropyRatio]
  have hh := mul_lt_mul_of_pos_left (entropy_phi_bound ht) hden
  have hp := mul_lt_mul_of_pos_left hswitch (mul_pos hden hr)
  have hid : (1 - a) * entropyRatio *
      (1 + (switchThreshold a + 9 / ((1 - a) * mu))) =
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
    unfold switchThreshold
    field_simp [ne_of_gt hden, ne_of_gt hmu]
    ring
  rw [← hid]
  nlinarith
end ThreeSum.Parameters
