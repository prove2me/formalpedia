-- Prove2me | solution 1 for ThreeSumApsp.WordRam.rpow_pow_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:22.697881+00:00
-- url     : https://prove2.me/submissions/df777b82-b1cf-414a-8a5c-985a3064fd1a

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
theorem _root_.solution {r : ℚ} (hr0 : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0))
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul, Real.rpow_natCast]
end ThreeSumApsp.WordRam
