-- Prove2me | solution 1 for ThreeSum.Parameters.all_ledger_caps_le_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:48.351221+00:00
-- url     : https://prove2.me/submissions/a3ef1974-8481-4059-9884-e7aa9b26e5e2

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution :
    ∀ t ∈ ([19 / 10, 49 / 25, 9809 / 5000, 19603 / 10000,
      42 / 25, 93 / 50, 111 / 100, 121 / 100, 21 / 50, 1] : List ℝ),
      t ≤ certificateExponent := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [certificateExponent]
end ThreeSum.Parameters
