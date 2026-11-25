-- Prove2me | solution 1 for PI.EF.goodHeightExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:11.816267+00:00
-- url     : https://prove2.me/submissions/2c387c82-77ac-423c-aed0-6ba02e94d563

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Theorems.Thm_PI_EF_exists_good_height
import Theorems.Thm_PI_EF_four_mul_le_cube

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
theorem _root_.solution {C : ℝ} (hC0 : 0 ≤ C) (hC : ZerosWindowWith C) :
    GoodHeightExists (12 * C + 4) := by
  intro N _ χ hχ T hT
  obtain ⟨T', hT', hgood⟩ := exists_good_height hC0 hC χ hχ (by linarith : (0 : ℝ) ≤ T)
  refine ⟨T', hT'.1, hT'.2, fun ρ h0 h1 hL => le_trans ?_ (hgood ρ h0 h1 hL)⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hT2 : 2 ≤ T' := le_trans hT hT'.1
  have hNT : 2 ≤ (N : ℝ) * T' := by nlinarith
  have hL' : 1 / 2 ≤ Real.log (N * T') := by
    have := Real.log_le_log (by norm_num) hNT
    linarith [Real.log_two_gt_d9]
  have hpos3 : (0 : ℝ) < N * (T + 3) := mul_pos (by linarith) (by linarith)
  have hL : Real.log (N * (T + 3)) ≤ 3 * Real.log (N * T') := by
    have hle : (N : ℝ) * (T + 3) ≤ (N * T') ^ 3 := by
      have h4 := four_mul_le_cube hT2
      have hN3 : (N : ℝ) ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
      calc (N : ℝ) * (T + 3) ≤ N * (4 * T') :=
            mul_le_mul_of_nonneg_left (by linarith [hT'.1]) (by linarith)
        _ ≤ N * T' ^ 3 := mul_le_mul_of_nonneg_left h4 (by linarith)
        _ ≤ N ^ 3 * T' ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
        _ = (N * T') ^ 3 := by ring
    calc Real.log (N * (T + 3)) ≤ Real.log ((N * T') ^ 3) := Real.log_le_log hpos3 hle
      _ = 3 * Real.log (N * T') := by rw [Real.log_pow]; norm_num
  have hlogpos : 0 ≤ Real.log (N * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hCL := mul_nonneg hC0 hlogpos
  have h1 : C * Real.log (N * (T + 3)) ≤ C * (3 * Real.log (N * T')) :=
    mul_le_mul_of_nonneg_left hL hC0
  apply one_div_le_one_div_of_le (by nlinarith)
  nlinarith
end PI.EF
