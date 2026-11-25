-- Prove2me | solution 1 for PI.Residue.optimise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:06.661876+00:00
-- url     : https://prove2.me/submissions/82f8a511-188a-4abb-989c-0d384ac96e8d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_ThirdLeLog
import Theorems.Thm_PI_Residue_third_le_log
import Theorems.Thm_PI_Residue_pow_le_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution : Optimise := by
  refine ⟨128 * Real.pi * Real.exp (1 / 2), ?_, ?_⟩
  · have hpi := Real.pi_gt_three
    have he : 1 ≤ Real.exp (1 / 2) := Real.one_le_exp (by norm_num)
    nlinarith
  intro m D hm hD
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hD1 : (3 / 2 : ℝ) ^ m ≤ D := (pow_le_lower m hm).trans hD
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  set l : ℝ := Real.log (D ^ ((1 : ℝ) / m)) with hl
  have hlD : Real.log D = m * l := by
    rw [hl, Real.log_rpow hDpos]
    field_simp
  have hl3 : 1 / 3 ≤ l := by
    have h1 : Real.log ((3 / 2 : ℝ) ^ m) ≤ Real.log D := Real.log_le_log (by positivity) hD1
    rw [Real.log_pow, hlD] at h1
    have h2 : Real.log (3 / 2) ≤ l := le_of_mul_le_mul_left h1 hm0
    exact third_le_log.trans h2
  have hlpos : 0 < l := by linarith
  refine ⟨1 + 1 / l, by linarith [one_div_pos.mpr hlpos], ?_⟩
  have e1 : (1 + 1 / l - 1) = 1 / l := by ring
  rw [e1, one_div_one_div]

  have hDexp : D ^ (1 / l / 2) = Real.exp (1 / 2) ^ m := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hDpos, hlD]
    congr 1
    field_simp

  have h4 : (4 : ℝ) ^ (1 + 1 / l) ≤ 16 ^ m := by
    have hle : 1 + 1 / l ≤ 4 := by
      have : 1 / l ≤ 3 := by
        rw [div_le_iff₀ hlpos]
        linarith
      linarith
    calc (4 : ℝ) ^ (1 + 1 / l) ≤ (4 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 16 ^ 2 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
      _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have h5 : (1 + l) ^ m ≤ (4 * l) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  rw [hDexp]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (4 : ℝ) ^ (1 + 1 / l) * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (1 + l) ^ m
      ≤ 16 ^ m * (2 * Real.pi) ^ m * Real.exp (1 / 2) ^ m * (4 * l) ^ m := by
        gcongr
    _ = (128 * Real.pi * Real.exp (1 / 2) * l) ^ m := by
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring
end PI.Residue
