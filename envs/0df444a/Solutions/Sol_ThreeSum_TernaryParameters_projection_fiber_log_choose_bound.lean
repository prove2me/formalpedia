-- Prove2me | solution 1 for ThreeSum.TernaryParameters.projection_fiber_log_choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:48.777536+00:00
-- url     : https://prove2.me/submissions/89529dc5-e81a-4d74-9762-524f1948b1c7

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_entropy_bound
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ) <
      (100000000 * m : ℕ) * Real.log 2 / 4 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hL : (0 : ℝ) < (100000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm)
  have hk : 978268 * m ≤ 100000000 * m :=
    Nat.mul_le_mul_right m (by decide : 978268 ≤ 100000000)
  have hr : ((978268 * m : ℕ) : ℝ) / (100000000 * m : ℕ) = alpha2 := by
    push_cast
    unfold alpha2
    field_simp
  have hb := (BinomialEntropy.log_choose_entropy_bounds hk).2
  rw [hr] at hb
  have he := (div_lt_iff₀ log_two_pos).mp projection_fiber_entropy_bound
  calc
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ)
      ≤ (100000000 * m : ℕ) * Real.binEntropy alpha2 := hb
    _ < (100000000 * m : ℕ) * ((1 / 4 : ℝ) * Real.log 2) :=
      mul_lt_mul_of_pos_left he hL
    _ = (100000000 * m : ℕ) * Real.log 2 / 4 := by ring
end ThreeSum.TernaryParameters
