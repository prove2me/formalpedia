-- Prove2me | solution 1 for ThreeSum.Switch.ratio_mem_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:34.830104+00:00
-- url     : https://prove2.me/submissions/0813a2eb-cadf-4ed4-adc2-1abac6498659

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {r q : ℕ} (hr : 0 < r) (hq : q ≤ r / 2) :
    (q : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htwo : 2 * q ≤ r := by
    have hm := Nat.div_mul_le_self r 2
    omega
  have htwoR : (2 : ℝ) * q ≤ r := by exact_mod_cast htwo
  constructor
  · positivity
  · rw [div_le_iff₀ hrR]
    linarith
end ThreeSum.Switch
