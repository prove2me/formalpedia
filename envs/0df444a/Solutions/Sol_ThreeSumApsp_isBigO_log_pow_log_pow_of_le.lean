-- Prove2me | solution 1 for ThreeSumApsp.isBigO_log_pow_log_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:12.72738+00:00
-- url     : https://prove2.me/submissions/93a2de4a-363d-44fe-bef6-e23cc9a3ae3b

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Theorems.Thm_ThreeSumApsp_isBigO_of_abs_le

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlog
  refine isBigO_of_abs_le 1 n₀ fun n hn => ?_
  rw [one_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans (hn₀ n hn)) e)]
  exact pow_le_pow_right₀ (hn₀ n hn) he
end ThreeSumApsp
