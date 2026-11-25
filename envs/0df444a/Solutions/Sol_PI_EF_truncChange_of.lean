-- Prove2me | solution 1 for PI.EF.truncChange_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:10.537802+00:00
-- url     : https://prove2.me/submissions/89f0f981-f108-46a0-b07c-312b51d9a2b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_trunc_change

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
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) : TruncChange (4 * C) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'
  have hmain := trunc_change hC0 hC χ hχ (by linarith : (0 : ℝ) < T) ⟨hTT', hT'⟩
    (by linarith : (1 : ℝ) ≤ u)
  unfold zsum
  refine le_trans hmain ?_
  unfold Err
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hT0 : 0 < T := by linarith
  have huT4 : (4 : ℝ) ≤ u * T := by nlinarith
  have hNuT : 4 ≤ (N : ℝ) * u * T := by
    have h := mul_le_mul_of_nonneg_right hN1 (by linarith : (0 : ℝ) ≤ u * T)
    have e : (N : ℝ) * u * T = N * (u * T) := by ring
    rw [e]
    linarith
  have hL2 : 1 ≤ Real.log (N * u * T) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hLle : Real.log (N * (T + 3)) ≤ 2 * Real.log (N * u * T) := by
    have hT2 : 4 ≤ T ^ 2 := by nlinarith
    have hA : T + 3 ≤ T ^ 2 * T ^ 2 := by nlinarith
    have hB : T ^ 2 ≤ u ^ 2 := by nlinarith
    have hC' : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have hle : (N : ℝ) * (T + 3) ≤ (N * u * T) ^ 2 := by
      calc (N : ℝ) * (T + 3) ≤ N * (T ^ 2 * T ^ 2) := mul_le_mul_of_nonneg_left hA (by linarith)
        _ ≤ N ^ 2 * (u ^ 2 * T ^ 2) :=
            mul_le_mul hC' (mul_le_mul_of_nonneg_right hB (by positivity)) (by positivity)
              (by positivity)
        _ = (N * u * T) ^ 2 := by ring
    calc Real.log (N * (T + 3)) ≤ Real.log ((N * u * T) ^ 2) :=
          Real.log_le_log (mul_pos (by linarith) (by linarith)) hle
      _ = 2 * Real.log (N * u * T) := by rw [Real.log_pow]; norm_num
  have hlogNu : 0 ≤ Real.log (N * u) := Real.log_nonneg (by nlinarith)
  have huT : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  have h1 : Real.log (N * (T + 3)) ≤ 2 * Real.log (N * u * T) ^ 2 := by nlinarith
  have h2 : 2 * C * Real.log (N * (T + 3)) * (u / T) ≤
      4 * C * (u * Real.log (N * u * T) ^ 2 / T) := by
    have e : u * Real.log (N * u * T) ^ 2 / T = Real.log (N * u * T) ^ 2 * (u / T) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC0) huT)
    nlinarith
  have h3 : 4 * C * (u * Real.log (N * u * T) ^ 2 / T) ≤
      4 * C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u)) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlogNu) (by linarith)
  linarith
end PI.EF
