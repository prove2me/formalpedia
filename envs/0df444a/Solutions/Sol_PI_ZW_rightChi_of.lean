-- Prove2me | solution 1 for PI.ZW.rightChi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:16.146061+00:00
-- url     : https://prove2.me/submissions/6ce6903e-aaae-4d18-9c6e-7349a90d436c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Theorems.Thm_PI_ZW_log_le_nine
import Theorems.Thm_PI_ZW_mem_closedBall_of_right
import Theorems.Thm_PI_ZW_sphere_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution (hJ : JensenCount) : RightChi := by
  intro hL hI
  have hl : 0 < Real.log ((19 / 10) / (37 / 20) : ℝ) := Real.log_pos (by norm_num)
  refine ⟨9 / Real.log ((19 / 10) / (37 / 20)), fun N _ χ hχ t => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcre : (2 + t * I : ℂ).re = 2 := by simp
  have hc0 : DirichletCharacter.LFunction χ (2 + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hcre]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := norm_pos_iff.mpr hc0
  have hinv := hI N χ (2 + t * I) (by rw [hcre]; norm_num)
  rw [hcre] at hinv
  have hfc : 1 / 2 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
    have h := (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mp (hinv.trans (by norm_num))
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall (2 + t * I) (19 / 10)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hM1 : (1 : ℝ) ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    have : 0 ≤ 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by positivity
    linarith
  have hbd : ∀ z ∈ sphere (2 + t * I) (19 / 10), ‖DirichletCharacter.LFunction χ z‖ ≤
      1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := sphere_facts hz
    have hz0 : 0 < z.re := by linarith
    refine (hL N χ hχ z hz0).trans ?_
    have h1 : ‖z‖ / z.re ≤ 10 * (|t| + 4) := by
      rw [div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 10 * (|t| + 4))]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1))
    nlinarith
  have hS : RightNear χ t ⊆ {z | z ∈ closedBall (2 + t * I) (37 / 20) ∧ DirichletCharacter.LFunction χ z = 0} :=
    fun ρ hρ => ⟨mem_closedBall_of_right hρ.1 hρ.2.1 hρ.2.2.1, hρ.2.2.2⟩
  obtain ⟨hfin, hsum⟩ := hJ (DirichletCharacter.LFunction χ) (2 + t * I) _ han hc0 hM1 hbd (RightNear χ t) hS
  refine ⟨hfin, hsum.trans ?_⟩
  have hX : 2 ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have htN : |t| ≤ N * |t| := le_mul_of_one_le_left (abs_nonneg t) hNr
  have hM85 : 1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4)) ≤ 85 * ((N : ℝ) * (|t| + 2)) := by
    nlinarith [abs_nonneg t]
  have hM' : (1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) / ‖DirichletCharacter.LFunction χ (2 + t * I)‖ ≤
      170 * ((N : ℝ) * (|t| + 2)) := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hfc (by linarith : (0 : ℝ) ≤ (N : ℝ) * (|t| + 2))]
  have h9 := log_le_nine _ _ hX (by positivity) hM'
  calc Real.log ((1 + 2 * ((N : ℝ) + 1) * (1 + 10 * (|t| + 4))) /
        ‖DirichletCharacter.LFunction χ (2 + t * I)‖) / Real.log ((19 / 10) / (37 / 20))
      ≤ (9 * Real.log ((N : ℝ) * (|t| + 2))) / Real.log ((19 / 10) / (37 / 20)) :=
        div_le_div_of_nonneg_right h9 hl.le
    _ = 9 / Real.log ((19 / 10) / (37 / 20)) * Real.log ((N : ℝ) * (|t| + 2)) := by ring
end PI.ZW
