-- Prove2me | solution 1 for ThreeSum.TernaryParameters.projection_fiber_bits_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:28.232489+00:00
-- url     : https://prove2.me/submissions/9edd28fe-705e-42fe-8eb5-0dad68cb5068

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_log_choose_bound
import Theorems.Thm_ThreeSum_Parameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ) /
      ((100000000 * m : ℕ) * Real.log 2) < (1 / 4 : ℝ) := by
  have hL : (0 : ℝ) < (100000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm)
  apply (div_lt_iff₀ (mul_pos hL log_two_pos)).mpr
  calc
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ)
      < (100000000 * m : ℕ) * Real.log 2 / 4 := projection_fiber_log_choose_bound hm
    _ = (1 / 4 : ℝ) * ((100000000 * m : ℕ) * Real.log 2) := by ring
end ThreeSum.TernaryParameters
