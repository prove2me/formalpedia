-- Prove2me | solution 1 for PI.EF.zeta_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:51.482997+00:00
-- url     : https://prove2.me/submissions/d550ebdd-4cb7-4d1b-af6b-4d0891a5a4c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta

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
theorem _root_.solution (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := by
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hre : 0 < s.re := by linarith
  have hb := hZ s hre hs
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have ht := abs_nonneg s.im
  have hs_le : ‖s‖ ≤ 8 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hs1_le : ‖s - 1‖ ≤ 7 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hre]; linarith
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖s - 1‖ + 1 + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
        rw [mul_add, mul_add, mul_one_div_cancel hn1.ne']
        ring
    _ ≤ (7 + |s.im|) + 1 + (7 + |s.im|) * (8 + |s.im|) * (1 + 2) := by gcongr
    _ ≤ 51 * (|s.im| + 2) ^ 2 := by nlinarith
end PI.EF
