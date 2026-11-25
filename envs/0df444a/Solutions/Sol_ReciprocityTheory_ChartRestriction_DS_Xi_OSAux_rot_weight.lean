-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rot_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:38.164861+00:00
-- url     : https://prove2.me/submissions/4d4dcc28-32e8-44f0-bc8e-4b743f64a201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma rho_den (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (by positivity)
private lemma key (t c₀ : ℝ) (X : ℂ) : 2 * (rho t * X).im + c₀ =
    ((2 * X.im + c₀) + 4 * X.re * t + (c₀ - 2 * X.im) * t ^ 2) / (1 + t ^ 2) := by
  have hd : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have key : rho t * ((1 + t ^ 2 : ℝ) : ℂ) = (1 + t * Complex.I) ^ 2 := by
    unfold rho
    exact div_mul_cancel₀ _ (rho_den t)
  have hre : (rho t).re = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.re key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  have him : (rho t).im = (2 * t) / (1 + t ^ 2) := by
    rw [eq_div_iff hd]
    have := congrArg Complex.im key
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im] at this
    linear_combination this
  rw [Complex.mul_im, hre, him]
  field_simp
  ring
private theorem rpow_neg_le_rpow_neg_of_pos_of_le {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 ≤ δ) : y ^ (-δ) ≤ x ^ (-δ) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  have ha : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  have hb : x ^ δ ≤ y ^ δ := Real.rpow_le_rpow hx.le hxy hδ
  exact inv_anti₀ ha hb
private theorem complex_norm_le_abs_re_add_abs_im (X : ℂ) : ‖X‖ ≤ |X.re| + |X.im| := by
  calc ‖X‖ = ‖(X.re : ℂ) + X.im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(X.re : ℂ)‖ + ‖(X.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |X.re| + |X.im| := by simp
private theorem complex_norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simp
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (hS : SUB) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℂ) (c₀ : ℝ),
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal (C * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
  obtain ⟨C₁, hC₁⟩ := hS δ hδ0 hδ1
  set K : ℝ := (5 : ℝ)⁻¹ ^ (-δ) with hKdef
  have hK : 0 < K := by positivity
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K * max C₁ 1, mul_pos hK hM, fun X c₀ => ?_⟩
  set A : ℝ := 2 * X.im + c₀ with hA
  set B : ℝ := 4 * X.re with hB
  set D : ℝ := c₀ - 2 * X.im with hD
  set c : Fin 3 → ℂ := ![(A : ℂ), (B : ℂ), (D : ℂ)] with hc
  have c0 : c 0 = (A : ℂ) := rfl
  have c1 : c 1 = (B : ℂ) := rfl
  have c2 : c 2 = (D : ℂ) := rfl
  set N : ℝ := ‖c‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hAN : |A| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c0]; exact norm_le_pi_norm c 0
  have hBN : |B| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c1]; exact norm_le_pi_norm c 1
  have hDN : |D| ≤ N := by rw [← complex_norm_ofReal_eq_abs, ← c2]; exact norm_le_pi_norm c 2
  have hc₀ : |c₀| ≤ N := by
    rw [abs_le] at hAN hDN ⊢
    constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
  have hX : ‖X‖ ≤ N := by
    have h1 := complex_norm_le_abs_re_add_abs_im X
    have hre : |X.re| ≤ N / 4 := by
      rw [abs_le] at hBN ⊢; constructor <;> linarith [hBN.1, hBN.2]
    have him : |X.im| ≤ N / 2 := by
      rw [abs_le] at hAN hDN ⊢; constructor <;> linarith [hAN.1, hAN.2, hDN.1, hDN.2]
    linarith
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2,
      ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    intro t ht
    rw [← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    have hq : c 0 + c 1 * t + c 2 * t ^ 2 = ((A + B * t + D * t ^ 2 : ℝ) : ℂ) := by
      rw [c0, c1, c2]; push_cast; ring
    rw [hq, complex_norm_ofReal_eq_abs, key]
    set q : ℝ := A + B * t + D * t ^ 2 with hqdef
    have hdpos : 0 < 1 + t ^ 2 := by positivity
    have hd5 : 1 + t ^ 2 ≤ 5 := by nlinarith [ht.1, ht.2]
    rw [hKdef, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) _ hδ0.le
    rw [abs_div, abs_of_pos hdpos]
    have hw0 : 0 ≤ |q| / (1 + t ^ 2) := div_nonneg (abs_nonneg _) hdpos.le
    have hwd : |q| / (1 + t ^ 2) * (1 + t ^ 2) = |q| := by
      exact div_mul_cancel₀ _ hdpos.ne'
    have := mul_le_mul_of_nonneg_left hd5 hw0
    linarith
  have hfin : C₁ * (1 + N) ^ (-δ / 2) ≤ max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
    have hpos : 0 < 1 + N := by linarith
    have e : (1 + N) ^ (-δ / 2) = (1 + N) ^ (-δ / 4) * (1 + N) ^ (-δ / 4) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hδ4 : 0 ≤ δ / 4 := by positivity
    have ha : (1 + N) ^ (-δ / 4) ≤ (1 + |c₀|) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hb : (1 + N) ^ (-δ / 4) ≤ (1 + ‖X‖) ^ (-δ / 4) := by
      rw [neg_div]; exact rpow_neg_le_rpow_neg_of_pos_of_le (by positivity) (by linarith) hδ4
    have hab : (1 + N) ^ (-δ / 2) ≤ (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4) := by
      rw [e]; exact mul_le_mul ha hb (by positivity) (by positivity)
    exact mul_le_mul (le_max_left _ _) hab (by positivity) hM.le
  have hmono : ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := by
    exact setLIntegral_mono' measurableSet_Icc hpt
  calc ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ))
      ≤ ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) := hmono
    _ = ENNReal.ofReal K * ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (C₁ * (1 + ‖c‖) ^ (-δ / 2)) := by
        gcongr
        exact hC₁ c
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (max C₁ 1 * ((1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4))) := by
        gcongr
    _ = ENNReal.ofReal (K * max C₁ 1 * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by
        rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
