-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.mean_lower_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:27.12534+00:00
-- url     : https://prove2.me/submissions/c4fe9376-5a1a-45ce-9b78-9a8a652294f9

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lower

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p)
    (hup : p ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h))) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean L h p := by
  have hM : (0 : ℝ) < outputCount L h := by exact_mod_cast Nat.choose_pos hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hG : (2 : ℝ) ^ (2 * h) ≤ (2 * (h : ℝ) + 1) * groupSize h := by
    exact_mod_cast groupSize_lower h
  have hupper : (p : ℝ) ^ 2 ≤ 16 * ((outputCount L h : ℝ) * 2 ^ (2 * h)) := by
    exact_mod_cast hup
  have hscale := mul_le_mul_of_nonneg_left hG (by positivity :
    (0 : ℝ) ≤ 16 * outputCount L h)
  rw [mean]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith
end ThreeSum.LocalCoverBounds
