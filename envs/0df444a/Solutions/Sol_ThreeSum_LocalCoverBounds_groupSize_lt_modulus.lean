-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.groupSize_lt_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:22.932325+00:00
-- url     : https://prove2.me/submissions/61790cf1-2559-4812-81f4-f2531eddef3e

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_le_pow

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {L h p : ℕ}
    (hM : 2 ^ (2 * h) < outputCount L h)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : groupSize h < p := by
  have hG := groupSize_le_pow h
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  have hsq : groupSize h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
    calc
      groupSize h ^ 2 ≤ (2 ^ (2 * h)) ^ 2 := Nat.pow_le_pow_left hG _
      _ = 2 ^ (2 * h) * 2 ^ (2 * h) := by rw [pow_two]
      _ < outputCount L h * 2 ^ (2 * h) := Nat.mul_lt_mul_of_pos_right hM hpow
  have hs := hsq.trans_le hp
  nlinarith
end ThreeSum.LocalCoverBounds
