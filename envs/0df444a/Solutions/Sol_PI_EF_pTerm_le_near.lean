-- Prove2me | solution 1 for PI.EF.pTerm_le_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:22.501335+00:00
-- url     : https://prove2.me/submissions/daf24072-b8b5-4956-bee6-e11dda0b3164

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_kb_le_nearB
import Theorems.Thm_PI_EF_cLine_le_three
import Theorems.Thm_PI_EF_cLine_pos
import Theorems.Thm_PI_EF_kb_nonneg
import Theorems.Thm_PI_EF_log_ge_half


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ}
    (h1 : u / 2 < (n : ℝ)) (h2 : (n : ℝ) < 2 * u) :
    pTerm u T n ≤ 16 * Real.log u * nearB u T n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast hx
  have hL := log_ge_half hu
  have a1 : ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log u := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hx h2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at this
    have h3 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
    linarith
  have a2 : (u / n) ^ cLine u ≤ 8 := by
    have hle : u / n ≤ 2 := by rw [div_le_iff₀ hx]; linarith
    calc (u / n) ^ cLine u ≤ (2 : ℝ) ^ cLine u :=
          Real.rpow_le_rpow (by positivity) hle (cLine_pos hu).le
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (cLine_le_three hu)
      _ = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have a3 := kb_le_nearB hu0 hT hn h2
  have b1 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have b2 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  unfold pTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ (2 * Real.log u * 8) * nearB u T n :=
        mul_le_mul (mul_le_mul a1 a2 b2 (by linarith)) a3 (kb_nonneg hT _) (by positivity)
    _ = 16 * Real.log u * nearB u T n := by ring
end PI.EF
