-- Prove2me | solution 1 for ReciprocityTheory.Cheb.csb_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:34.267006+00:00
-- url     : https://prove2.me/submissions/293b7390-1684-4a3e-bbb5-1941104755b1

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (a b : ℕ) (ha : 1 ≤ a) (hab : a ^ 2 ≤ b) (s : ℝ) (hs : 1 < s) :
    ((b : ℕ) : ℝ) ^ (-s) ≤ ((a : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : ((a : ℝ)) ^ 2 ≤ (b : ℝ) := by exact_mod_cast hab
  have hb' : (1 : ℝ) ≤ b := le_trans (one_le_pow₀ ha') hab'
  calc ((b : ℝ)) ^ (-s) ≤ (b : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb' (by linarith)
    _ = (b : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ ((a : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hab'
    _ = (a : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
end ReciprocityTheory.Cheb
