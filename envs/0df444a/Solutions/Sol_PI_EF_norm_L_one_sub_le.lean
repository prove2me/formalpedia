-- Prove2me | solution 1 for PI.EF.norm_L_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:50.497971+00:00
-- url     : https://prove2.me/submissions/98f84ab2-47e2-4297-85f1-fb9c57e1c196

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Theorems.Thm_PI_EF_zmodL_const_mul
import Theorems.Thm_PI_EF_norm_gaussSum_le
import Theorems.Thm_PI_EF_Gamma_decay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.EF
open Complex DirichletCharacter
open scoped ZMod
variable {N : ℕ} [NeZero N]
private theorem re_pi_mul_I_mul_div_two (w : ℂ) :
    ((Real.pi : ℂ) * I * w / 2).re = -(Real.pi / 2 * w.im) := by
  rw [show ((Real.pi : ℂ) * I * w / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring
private theorem re_neg_pi_mul_I_mul_div_two (w : ℂ) :
    (-(Real.pi : ℂ) * I * w / 2).re = Real.pi / 2 * w.im := by
  rw [show (-(Real.pi : ℂ) * I * w / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring
private theorem norm_LFunction_const_mul_le_of_norm_le (χ : DirichletCharacter ℂ N) {c : ℂ} (hc : ‖c‖ ≤ N)
    (w : ℂ) :
    ‖ZMod.LFunction (fun k => c * (χ : ZMod N → ℂ) k) w‖
      ≤ N * ‖ZMod.LFunction (χ : ZMod N → ℂ) w‖ := by
  rw [zmodL_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
end PI.EF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
open scoped ZMod
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖LFunction χ⁻¹ w‖ := by
  change ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - w)‖
    ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖
  set L := ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖ with hL
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hs : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ w ≠ 1 := h
  rw [ZMod.LFunction_one_sub _ hs hs']
  set g := gaussSum χ (ZMod.stdAddChar (N := N)) with hg
  have hgN : ‖g‖ ≤ N := norm_gaussSum_le χ
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
    ring
  have hneg : (fun x => (χ : ZMod N → ℂ) (-x)) = χ (-1) • (χ : ZMod N → ℂ) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, neg_one_mul]
  have hc1 : ‖g * χ⁻¹ (-1)‖ ≤ N := by
    rw [norm_mul]
    calc ‖g‖ * ‖χ⁻¹ (-1)‖ ≤ N * 1 :=
          mul_le_mul hgN (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by positivity)
      _ = N := mul_one _
  have hc2 : ‖χ (-1) * (g * χ⁻¹ (-1))‖ ≤ N := by
    rw [norm_mul]
    calc ‖χ (-1)‖ * ‖g * χ⁻¹ (-1)‖ ≤ 1 * N :=
          mul_le_mul (DirichletCharacter.norm_le_one _ _) hc1 (norm_nonneg _) (by positivity)
      _ = N := one_mul _
  have hA : ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖ ≤ N * L := by
    rw [hF]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc1 w
  have hB : ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ N * L := by
    rw [hneg, map_smul, hF]
    have e : (χ (-1) • fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k)
        = fun k => (χ (-1) * (g * χ⁻¹ (-1))) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc2 w
  set E := Real.exp (Real.pi / 2 * |w.im|) with hE
  have he1 : ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le w.im
    have := Real.pi_pos
    nlinarith
  have he2 : ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_neg_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := le_abs_self w.im
    have := Real.pi_pos
    nlinarith
  have hP : ‖(N : ℂ) ^ (w - 1)‖ ≤ (N : ℝ) ^ 4 := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.sub_re, Complex.one_re]
    calc (N : ℝ) ^ (w.re - 1) ≤ (N : ℝ) ^ ((4 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = (N : ℝ) ^ 4 := Real.rpow_natCast _ _
  have hQ : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hGE : ‖Complex.Gamma w‖ * E ≤ 3 * ‖w + 1‖ ^ 5 :=
    Gamma_decay h1 (by linarith)
  have hsum : ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w
      + cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖
      ≤ 2 * E * N * L := by
    calc _ ≤ ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)
              * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := norm_add_le _ _
      _ = ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ * ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖
              * ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ E * (N * L) + E * (N * L) := by gcongr
      _ = 2 * E * N * L := by ring
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(N : ℂ) ^ (w - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖_‖
      ≤ (N : ℝ) ^ 4 * 1 * ‖Complex.Gamma w‖ * (2 * E * N * L) := by gcongr
    _ = 2 * (N : ℝ) ^ 5 * L * (‖Complex.Gamma w‖ * E) := by ring
    _ ≤ 2 * (N : ℝ) ^ 5 * L * (3 * ‖w + 1‖ ^ 5) := by gcongr
    _ = 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * L := by ring
end PI.EF
