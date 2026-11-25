-- Prove2me | solution 1 for PI.EF.PK.horiz_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:33.873072+00:00
-- url     : https://prove2.me/submissions/480fb523-ce78-4951-94a2-58617e2ba51e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_norm_ker
import Theorems.Thm_PI_EF_PK_integral_exp_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l a b h : ℝ) (hl : l ≠ 0) (hh : h ≠ 0) (hab : a ≤ b) :
    ‖∫ x : ℝ in a..b, ker l ((x : ℂ) + h * I)‖ ≤
      (Real.exp (l * b) - Real.exp (l * a)) / l / |h| := by
  have hh' : 0 < |h| := abs_pos.2 hh
  have hpt : ∀ x : ℝ, ‖ker l ((x : ℂ) + h * I)‖ ≤ Real.exp (l * x) / |h| := by
    intro x
    rw [norm_ker]
    have hre : ((x : ℂ) + h * I).re = x := by simp
    have him : ((x : ℂ) + h * I).im = h := by simp
    rw [hre]
    have hn : |h| ≤ ‖(x : ℂ) + h * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
      rwa [him] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hh' hn
  calc ‖∫ x : ℝ in a..b, ker l ((x : ℂ) + h * I)‖ ≤ ∫ x in a..b, Real.exp (l * x) / |h| :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Filter.Eventually.of_forall (fun x _ => hpt x))
          (by apply Continuous.intervalIntegrable; fun_prop)
    _ = (Real.exp (l * b) - Real.exp (l * a)) / l / |h| := by
        rw [intervalIntegral.integral_div, integral_exp_mul l a b hl]
end PI.EF.PK
