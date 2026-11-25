-- Prove2me | solution 1 for PI.EF.norm_twistedGamma_le_of_re_eq_eleven_halves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:20.035216+00:00
-- url     : https://prove2.me/submissions/3a41eafa-ebc7-431a-88c1-dcc6fd3dda2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Theorems.Thm_PI_EF_norm_le_norm_of
import Theorems.Thm_PI_EF_half_line
import Theorems.Thm_PI_EF_norm_twistedGamma
import Theorems.Thm_PI_EF_one_le_norm_add_one
import Theorems.Thm_PI_EF_eq_re_add_im
import Theorems.Thm_PI_EF_Gamma_add_five

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
theorem _root_.solution (w : ℂ) (hw : w.re = 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  set z : ℂ := 1 / 2 + (w.im : ℂ) * I with hz
  have e : w = z + 5 := by
    conv_lhs => rw [eq_re_add_im w, hw]
    rw [hz]
    push_cast
    ring
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = w.im := by simp [hz]
  have h2 := half_line w.im
  rw [← hz] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have hb : ∀ k : ℝ, 0 ≤ k → k ≤ 4 → ‖z + (k : ℂ)‖ ≤ ‖w + 1‖ := by
    intro k hk0 hk4
    apply norm_le_norm_of
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, hzre, hw]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by norm_num)]
      linarith
    · simp [hzim]
  have b0 : ‖z‖ ≤ ‖w + 1‖ := by simpa using hb 0 (le_refl _) (by norm_num)
  have b1 : ‖z + 1‖ ≤ ‖w + 1‖ := by simpa using hb 1 (by norm_num) (by norm_num)
  have b2 : ‖z + 2‖ ≤ ‖w + 1‖ := by simpa using hb 2 (by norm_num) (by norm_num)
  have b3 : ‖z + 3‖ ≤ ‖w + 1‖ := by simpa using hb 3 (by norm_num) (by norm_num)
  have b4 : ‖z + 4‖ ≤ ‖w + 1‖ := by simpa using hb 4 (by norm_num) (by norm_num)
  have hG : ‖Complex.Gamma w‖ ≤ ‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖ := by
    rw [e, Gamma_add_five z (by rw [hzre]; norm_num), ← e]
    simp only [norm_mul]
    set X := ‖w + 1‖
    have hX : 0 ≤ X := norm_nonneg _
    have hg := norm_nonneg (Complex.Gamma z)
    calc ‖z + 4‖ * (‖z + 3‖ * (‖z + 2‖ * (‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖))))
        ≤ X * (X * (X * (X * (X * ‖Complex.Gamma z‖)))) := by gcongr
      _ = X ^ 5 * ‖Complex.Gamma z‖ := by ring
  have hpos : 0 < ‖w + 1‖ ^ 5 := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im)
      ≤ (‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖) * Real.exp (Real.pi / 2 * |w.im|) :=
        mul_le_mul hG h3 (Real.exp_pos _).le (by positivity)
    _ = (‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * |w.im|)) * ‖w + 1‖ ^ 5 := by ring
    _ ≤ 3 * ‖w + 1‖ ^ 5 := mul_le_mul_of_nonneg_right h2 hpos.le
end PI.EF
