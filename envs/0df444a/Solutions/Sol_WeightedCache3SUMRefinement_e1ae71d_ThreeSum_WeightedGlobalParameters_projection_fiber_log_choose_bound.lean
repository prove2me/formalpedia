-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.projection_fiber_log_choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:57.328072+00:00
-- url     : https://prove2.me/submissions/cd3b6875-7698-47e3-b50e-20bc2d768b15

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_projection_fiber_entropy_bound
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
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
    Real.log (((30000000000000000 * m).choose (292929977780940 * m) : ℕ) : ℝ) <
      (30000000000000000 * m : ℕ) * Real.log 2 / 4 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hL : (0 : ℝ) < (30000000000000000 * m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 30000000000000000) hm)
  have hk : 292929977780940 * m ≤ 30000000000000000 * m :=
    Nat.mul_le_mul_right m (by decide : 292929977780940 ≤ 30000000000000000)
  have hr : ((292929977780940 * m : ℕ) : ℝ) / (30000000000000000 * m : ℕ) = alpha2 := by
    push_cast
    unfold alpha2
    field_simp
    norm_num
  have hb := (BinomialEntropy.log_choose_entropy_bounds hk).2
  rw [hr] at hb
  have he := (div_lt_iff₀ log_two_pos).mp projection_fiber_entropy_bound
  calc
    Real.log (((30000000000000000 * m).choose (292929977780940 * m) : ℕ) : ℝ)
      ≤ (30000000000000000 * m : ℕ) * Real.binEntropy alpha2 := hb
    _ < (30000000000000000 * m : ℕ) * ((1 / 4 : ℝ) * Real.log 2) :=
      mul_lt_mul_of_pos_left he hL
    _ = (30000000000000000 * m : ℕ) * Real.log 2 / 4 := by ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
