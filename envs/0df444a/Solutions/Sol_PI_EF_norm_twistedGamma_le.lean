-- Prove2me | solution 1 for PI.EF.norm_twistedGamma_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:19.205894+00:00
-- url     : https://prove2.me/submissions/deb9e680-6766-47ed-9cef-b355cb0052dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Theorems.Thm_PI_EF_norm_Gamma_le
import Theorems.Thm_PI_EF_norm_twistedGamma
import Theorems.Thm_PI_EF_one_le_norm_add_one
import Theorems.Thm_PI_EF_norm_twistedGamma_le_of_re_eq_half
import Theorems.Thm_PI_EF_norm_twistedGamma_le_of_re_eq_eleven_halves
import Theorems.Thm_PI_EF_diffContOnCl_twistedGamma

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
open Complex Filter Set
namespace PI.EF
theorem _root_.solution {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  refine PhragmenLindelof.vertical_strip diffContOnCl_twistedGamma ?_ norm_twistedGamma_le_of_re_eq_half norm_twistedGamma_le_of_re_eq_eleven_halves h1 h2
  refine ⟨1 / 2, ?_, Real.pi, ?_⟩
  · have := Real.pi_gt_three
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  · apply Asymptotics.IsBigO.of_bound (max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)))
    apply Filter.eventually_inf_principal.mpr
    apply Filter.Eventually.of_forall
    intro z hz
    have hz1 : (1 / 2 : ℝ) < z.re := hz.1
    have hz2 : z.re < 11 / 2 := hz.2
    rw [norm_twistedGamma, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have a1 : ‖Complex.Gamma z‖ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) :=
      (norm_Gamma_le (by linarith)).trans
        (Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num [Set.mem_Ioi]) (by norm_num [Set.mem_Ioi])
          ⟨hz1.le, hz2.le⟩)
    have a2 : Real.exp (Real.pi / 2 * z.im) ≤ Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have q1 := Real.add_one_le_exp (1 / 2 * |z.im|)
      have q2 := le_abs_self z.im
      have q3 := abs_nonneg z.im
      have hpi := Real.pi_pos
      nlinarith
    have a3 : (1 : ℝ) ≤ ‖z + 1‖ ^ 5 := one_le_pow₀ (one_le_norm_add_one (by linarith))
    rw [div_le_iff₀ (by linarith)]
    have a4 : 0 ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) := (norm_nonneg _).trans a1
    calc ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im)
        ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) :=
          mul_le_mul a1 a2 (Real.exp_pos _).le a4
      _ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) * ‖z + 1‖ ^ 5 :=
          le_mul_of_one_le_right (mul_nonneg a4 (Real.exp_pos _).le) a3
end PI.EF
