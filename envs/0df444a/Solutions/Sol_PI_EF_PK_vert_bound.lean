-- Prove2me | solution 1 for PI.EF.PK.vert_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:08.976313+00:00
-- url     : https://prove2.me/submissions/f2bb9f18-97ce-41bc-a813-a32f39f4cfcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_norm_ker

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
theorem _root_.solution (l x T : ℝ) (hx : x ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in -T..T, ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x| * (2 * T) := by
  have hpt : ∀ t ∈ Set.uIoc (-T) T, ‖ker l ((x : ℂ) + t * I)‖ ≤ Real.exp (l * x) / |x| := by
    intro t _
    rw [norm_ker]
    have hre : ((x : ℂ) + t * I).re = x := by simp
    rw [hre]
    have hn : |x| ≤ ‖(x : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + t * I)
      rwa [hre] at this
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (abs_pos.2 hx) hn
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have e : |T - -T| = 2 * T := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [e] at this
  exact this
end PI.EF.PK
