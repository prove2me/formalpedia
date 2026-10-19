-- Prove2me | solution 1 for PermanentRollout.logarithmic_lower_bound_of_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/f489efe9-2d40-492e-8416-1a89fc7a8047

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_square_le_fortyEight_mul_sliceRank

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d q : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n)
    (hgradient : (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
      3 * (q : ℝ)) :
    (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤ (q : ℝ) := by
  have hd_real : (3 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hlog : 0 ≤ Real.logb 2 ((d : ℝ) - 1) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hsquare_nat := square_le_fortyEight_mul_sliceRank hd hn
  have hsquare : (n : ℝ) ^ 2 ≤ 48 * (sliceRank n d : ℝ) := by
    exact_mod_cast hsquare_nat
  have hproduct := mul_le_mul_of_nonneg_right hsquare hlog
  nlinarith
end PermanentRollout
