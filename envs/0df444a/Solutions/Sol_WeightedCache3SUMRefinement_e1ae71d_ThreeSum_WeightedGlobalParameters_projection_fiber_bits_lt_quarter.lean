-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:00.905412+00:00
-- url     : https://prove2.me/submissions/372b048c-14a6-4c2e-9864-0022fae5dcd9

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_projection_fiber_log_choose_bound
import Theorems.Thm_ThreeSum_Parameters_log_two_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000000 * m).choose (292929977780940 * m) : ℕ) : ℝ) /
      ((30000000000000000 * m : ℕ) * Real.log 2) < (1 / 4 : ℝ) := by
  have hL : (0 : ℝ) < (30000000000000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 30000000000000000) hm)
  apply (div_lt_iff₀ (mul_pos hL log_two_pos)).mpr
  calc
    Real.log (((30000000000000000 * m).choose (292929977780940 * m) : ℕ) : ℝ)
      < (30000000000000000 * m : ℕ) * Real.log 2 / 4 := projection_fiber_log_choose_bound hm
    _ = (1 / 4 : ℝ) * ((30000000000000000 * m : ℕ) * Real.log 2) := by ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
