-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.one_le_kappa_mul_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:18.565084+00:00
-- url     : https://prove2.me/submissions/b76d17c9-3681-4293-bdb9-853f00a631a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneLeKappaMulPhase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_f_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_firstMinimum_pos_bis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_two_le_dstar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private theorem one_le_four_mul_r7_d_sq_div_of_bounds (r F la d q R : ℝ) (hla : 0 < la) (hr : 16 ≤ r) (hF : 1 ≤ F)
    (hd : 2 ≤ d) (hq : 1 ≤ q) (hR : 270 ≤ R ^ 2)
    (hC2 : 1 ≤ q / (R ^ 2 * (r ^ 7) ^ 4))
    (hlt : la < Real.sqrt (F * R ^ 2 * (r ^ 7) ^ 3 / q)) :
    1 ≤ 4 * r ^ 7 * d ^ 2 * (2 * F / (r ^ 2 * la ^ 2)) := by
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := hqpos.ne'
  have hr0 : 0 < r := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hR2 : 0 < R ^ 2 := by linarith
  have hRne : R ≠ 0 := by
    rintro rfl
    norm_num at hR
  have hden : 0 < R ^ 2 * (r ^ 7) ^ 4 := mul_pos hR2 (pow_pos (pow_pos hr0 7) 4)

  have hC2' : R ^ 2 * (r ^ 7) ^ 4 ≤ q := by
    have h := mul_le_mul_of_nonneg_right hC2 hden.le
    have e : q / (R ^ 2 * (r ^ 7) ^ 4) * (R ^ 2 * (r ^ 7) ^ 4) = q := by
      field_simp
    linarith
  have harg : 0 ≤ F * R ^ 2 * (r ^ 7) ^ 3 / q :=
    div_nonneg (mul_nonneg (mul_nonneg hF0 (sq_nonneg R)) (pow_pos (pow_pos hr0 7) 3).le) hqpos.le
  have hsq : la * la < F * R ^ 2 * (r ^ 7) ^ 3 / q := by
    have h := mul_self_lt_mul_self hla.le hlt
    rwa [Real.mul_self_sqrt harg] at h
  have hr7 : 0 < r ^ 7 := pow_pos hr0 7

  have hT : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 ≤ F := by
    have e : F * R ^ 2 * (r ^ 7) ^ 3 / q * r ^ 7 * q = F * (R ^ 2 * (r ^ 7) ^ 4) := by
      first
        | (field_simp; ring)
        | field_simp
    have h2 : F * (R ^ 2 * (r ^ 7) ^ 4) ≤ F * q := mul_le_mul_of_nonneg_left hC2' hF0
    by_contra hc
    push_neg at hc
    have h3 := mul_lt_mul_of_pos_right hc hqpos
    linarith
  have hA : la ^ 2 * r ^ 7 < F := by
    have h := mul_lt_mul_of_pos_right hsq hr7
    nlinarith
  have hden2 : 0 < r ^ 2 * la ^ 2 := mul_pos (pow_pos hr0 2) (pow_pos hla 2)
  have hr5 : (1 : ℝ) ≤ r ^ 5 := by
    have h : (16 : ℝ) ^ 5 ≤ r ^ 5 := by gcongr
    norm_num at h
    linarith
  have hr71 : (1 : ℝ) ≤ r ^ 7 := by
    have h : (16 : ℝ) ^ 7 ≤ r ^ 7 := by gcongr
    norm_num at h
    linarith
  have hd4 : (4 : ℝ) ≤ d ^ 2 := by nlinarith
  have h1 : r ^ 2 * la ^ 2 ≤ la ^ 2 * r ^ 7 := by
    have h : r ^ 2 * la ^ 2 * 1 ≤ r ^ 2 * la ^ 2 * r ^ 5 :=
      mul_le_mul_of_nonneg_left hr5 hden2.le
    calc r ^ 2 * la ^ 2 = r ^ 2 * la ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * la ^ 2 * r ^ 5 := h
      _ = la ^ 2 * r ^ 7 := by ring
  have h8 : (1 : ℝ) ≤ 8 * (r ^ 7 * d ^ 2) := by
    nlinarith [mul_le_mul hr71 hd4 (by norm_num) (by linarith)]
  have hK : F ≤ 4 * r ^ 7 * d ^ 2 * (2 * F) := by
    have h := mul_le_mul_of_nonneg_right h8 hF0
    nlinarith
  have key : r ^ 2 * la ^ 2 ≤ 4 * r ^ 7 * d ^ 2 * (2 * F) := by linarith
  have hM : 4 * r ^ 7 * d ^ 2 * (2 * F / (r ^ 2 * la ^ 2)) * (r ^ 2 * la ^ 2)
      = 4 * r ^ 7 * d ^ 2 * (2 * F) := by
    have : r ^ 2 * la ^ 2 ≠ 0 := hden2.ne'
    first
      | (field_simp; ring)
      | field_simp
  by_contra hc
  push_neg at hc
  have h := mul_lt_mul_of_pos_right hc hden2
  linarith
end
end ReciprocityTheory.ChartRestriction.G.I2
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hph : 0 < P.ph) :
    1 ≤ P.ka0 * P.ph := by
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hka : P.ka0 = 4 * PT.rd E ^ 7 * (dstar (E := E) P.m : ℝ) ^ 2 := rfl
  have hphd : P.ph = if X.la1 < th (E := E) P.q P.R0
      then 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) else 0 := rfl
  by_cases hlt : X.la1 < th (E := E) P.q P.R0
  · rw [hphd, if_pos hlt, hka]
    have hC2 : (1 : ℝ) ≤ (P.q : ℝ) / (P.R0 ^ 2 * (PT.rd E ^ 7) ^ 4) := P.C2
    have hlt' : X.la1 < Real.sqrt ((PT.f E : ℝ) * P.R0 ^ 2 * (PT.rd E ^ 7) ^ 3 / (P.q : ℝ)) := hlt
    exact one_le_four_mul_r7_d_sq_div_of_bounds (PT.rd E) (PT.f E) X.la1 (dstar (E := E) P.m) P.q P.R0 hla P.hrd
      (by exact_mod_cast f_pos P) (by exact_mod_cast tof_two_le_dstar P)
      (by exact_mod_cast P.hq) P.hR0.1 hC2 hlt'
  · rw [hphd, if_neg hlt] at hph
    exact absurd hph (lt_irrefl 0)
end ReciprocityTheory.ChartRestriction.G.I2
