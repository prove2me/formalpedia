-- Prove2me | solution 1 for PI.EF.zetaGrowth_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:26:36.415803+00:00
-- url     : https://prove2.me/submissions/ca23230b-5677-4b7e-86be-71fb53cc4e74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta
import Theorems.Thm_PI_EF_zeta_right
import Theorems.Thm_PI_EF_zeta_left

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
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution (hZ : PI.ZetaBoundRight) : ZetaGrowth 300000 := by
  intro s hs1 hs2
  have ht := abs_nonneg s.im
  have h2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hp7 : (|s.im| + 2) ^ 2 ≤ (|s.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := zeta_right hZ hr hs2
      _ ≤ 300000 * (|s.im| + 2) ^ 7 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ |s.im| + 2) 2]
  · push_neg at hr
    by_cases hn : 1 / 2 ≤ ‖s‖
    · calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := zeta_left hZ hs1 hr hn
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr; norm_num
    · push_neg at hn
      have hK : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 2)),
          ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by
        intro z hz
        rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hz
        have hre : |z.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z).trans hz.le
        have him : |z.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z).trans hz.le
        have hzi := abs_nonneg z.im
        rcases lt_or_ge z.re (1 / 2) with hlt | hge
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (|z.im| + 2) ^ 7 :=
                zeta_left hZ (by linarith [(abs_le.1 hre).1]) hlt (by rw [hz])
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by gcongr; linarith
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 51 * (|z.im| + 2) ^ 2 :=
                zeta_right hZ hge (by linarith [(abs_le.1 hre).2])
            _ ≤ 51 * (5 / 2 : ℝ) ^ 2 := by gcongr; linarith
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by norm_num
      have hd : DiffContOnCl ℂ (fun z => (z - 1) * riemannZeta z) (Metric.ball (0 : ℂ) (1 / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        intro z hz
        have hz1 : z ≠ 1 := by
          intro h
          rw [h, Metric.mem_closedBall, dist_zero_right, norm_one] at hz
          norm_num at hz
        exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt
      have hmem : s ∈ closure (Metric.ball (0 : ℂ) (1 / 2)) := subset_closure (mem_ball_zero_iff.2 hn)
      have hb := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hK hmem
      calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := hb
        _ ≤ 300000 * 2 ^ 7 := by norm_num
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr
end PI.EF
