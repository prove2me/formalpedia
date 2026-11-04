-- Prove2me | solution 1 for ThreeSumApsp.WordRam.bigO_of_le_rpow_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:42.418403+00:00
-- url     : https://prove2.me/submissions/0b7aaba0-ac45-417d-be47-52d4e938c2e2

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
import Theorems.Thm_ThreeSumApsp_WordRam_rpow_pow_den
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
theorem _root_.solution {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : EndStatement.BigO T r := by
  refine ⟨⌈|C| ^ r.den⌉₊, fun n hn => ?_⟩
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hreal : (T n : ℝ) ^ r.den ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
    calc (T n : ℝ) ^ r.den
        ≤ (|C| * (n : ℝ) ^ (r : ℝ)) ^ r.den :=
          pow_le_pow_left₀ (Nat.cast_nonneg _)
            ((hT n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hrpow)) _
      _ = |C| ^ r.den * (n : ℝ) ^ r.num.toNat := by rw [mul_pow, rpow_pow_den hr0]
      _ ≤ (⌈|C| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast hreal
end ThreeSumApsp.WordRam
