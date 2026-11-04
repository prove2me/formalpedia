-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:15.112541+00:00
-- url     : https://prove2.me/submissions/d7ecc789-5f5c-4efb-8045-8b2ff43439a4

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_log_choose_bound
import Theorems.Thm_ThreeSum_Parameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ) /
      ((30000000000000 * m : ℕ) * Real.log 2) < (1 / 4 : ℝ) := by
  have hL : (0 : ℝ) < (30000000000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 30000000000000) hm)
  apply (div_lt_iff₀ (mul_pos hL log_two_pos)).mpr
  calc
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ)
      < (30000000000000 * m : ℕ) * Real.log 2 / 4 := projection_fiber_log_choose_bound hm
    _ = (1 / 4 : ℝ) * ((30000000000000 * m : ℕ) * Real.log 2) := by ring
end ThreeSum.WeightedGlobalParameters
