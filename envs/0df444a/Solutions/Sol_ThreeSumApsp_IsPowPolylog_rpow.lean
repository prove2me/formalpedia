-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:07.978082+00:00
-- url     : https://prove2.me/submissions/fb0ffccb-ebbf-462e-b9ef-7a90981a937d

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_IsBigOPow_rpow__dbdce0
import Theorems.Thm_Real_one_le_log_natCast_of_three_le
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_isBigO_of_abs_le


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog
namespace ThreeSumApsp.IsPowPolylog
theorem _root_.solution (hf : IsPowPolylog f a) {r : ℝ} (hr : 0 ≤ r) :
    IsPowPolylog (fun n => f n ^ r) (a * r) := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨E, hE⟩ := exists_nat_ge ((e : ℝ) * r)
  have hpow : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a := fun n => Real.rpow_nonneg n.cast_nonneg a
  have hlogpow : ∀ n : ℕ, 0 ≤ Real.log n ^ e := fun n => pow_nonneg (Real.log_natCast_nonneg n) e
  refine ⟨E, (hf.rpow hr (Eventually.of_forall fun n => mul_nonneg (hpow n) (hlogpow n))).trans ?_⟩
  -- `(n^a (log n)^e)^r = n^(a r) (log n)^(e r) ≤ n^(a r) (log n)^E` as soon as `log n ≥ 1`
  refine isBigO_of_abs_le 1 3 fun n hn => ?_
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le hn
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (mul_nonneg (hpow n) (hlogpow n)) r),
    Real.mul_rpow (hpow n) (hlogpow n), ← Real.rpow_mul n.cast_nonneg,
    ← Real.rpow_natCast (Real.log n) e, ← Real.rpow_mul (zero_le_one.trans hlog),
    ← Real.rpow_natCast (Real.log n) E]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog hE)
    (Real.rpow_nonneg n.cast_nonneg _)
end ThreeSumApsp.IsPowPolylog
