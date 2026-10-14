-- Prove2me | solution 1 for ThreeSumSharpTail.sharp_saving_strict
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T15:37:47.002905+00:00
-- url     : https://prove2.me/submissions/8fa49aa0-a38b-4b22-8748-d03eec158f65

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumSharpTail

theorem solution (c θ : ℝ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    0 < oldSaving c θ ∧ oldSaving c θ < sharpSaving c θ := by
  have hθ1 : θ < 1 := by linarith
  have hc1 : 1 < c := by linarith
  have hcsub : 0 < c - 1 := by linarith
  have hq : 0 < 1 - θ := by linarith
  have hden : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hratio : 1 < (c - 1) / 9 := by
    rw [one_lt_div (by norm_num : (0 : ℝ) < 9)]
    linarith
  have holdnum : 0 < θ * Real.log ((c - 1) / 9) :=
    mul_pos hθ0 (Real.log_pos hratio)
  constructor
  · exact div_pos holdnum hden
  · have hcpos : 0 < c := by linarith
    have hleftarg : 0 < 1 / c := by positivity
    have hrightarg : 0 < (1 - θ) / c := by positivity
    have hleftone : 0 < 1 - 1 / c := by
      have hsmall : 1 / c < 1 := by
        rw [div_lt_iff₀ hcpos]
        linarith
      linarith
    have hrightone : 0 < 1 - (1 - θ) / c := by
      have hsmall : (1 - θ) / c < 1 := by
        rw [div_lt_iff₀ hcpos]
        linarith
      linarith
    have hL1 : Real.log (1 / c) = -Real.log c := by
      simpa only [one_div] using (Real.log_inv c)
    have hL2 : Real.log (1 - 1 / c) = Real.log (c - 1) - Real.log c := by
      have heq : 1 - 1 / c = (c - 1) / c := by field_simp
      rw [heq, Real.log_div hcsub.ne' hcpos.ne']
    have hL3 : Real.log ((1 - θ) / c) = Real.log (1 - θ) - Real.log c := by
      rw [Real.log_div hq.ne' hcpos.ne']
    have hL4 : Real.log (1 - (1 - θ) / c) = Real.log (c - 1 + θ) - Real.log c := by
      have heq : 1 - (1 - θ) / c = (c - 1 + θ) / c := by field_simp <;> ring
      have hpos : 0 < c - 1 + θ := by positivity
      rw [heq, Real.log_div hpos.ne' hcpos.ne']
    have hEntropy :
        c * entropy (1 / c) - c * entropy ((1 - θ) / c) =
          (1 - θ) * Real.log (1 - θ) +
            (c - 1 + θ) * Real.log (c - 1 + θ) - (c - 1) * Real.log (c - 1) := by
      simp only [entropy]
      rw [hL1, hL2, hL3, hL4]
      field_simp [hcpos.ne']
      ring
    have hlogsmall :
        Real.log (1 - θ) > -θ / (1 - θ) := by
      have hinvpos : 0 < (1 - θ)⁻¹ := inv_pos.mpr hq
      have hinvne : (1 - θ)⁻¹ ≠ 1 := by
        exact ne_of_gt ((one_lt_inv₀ hq).2 (by linarith))
      have := Real.log_lt_sub_one_of_pos hinvpos hinvne
      rw [Real.log_inv] at this
      have hinv : (1 - θ)⁻¹ - 1 = θ / (1 - θ) := by field_simp; ring
      rw [hinv] at this
      have hmul := mul_lt_mul_of_pos_right this hq
      field_simp at hmul
      rw [gt_iff_lt, div_lt_iff₀ hq]
      nlinarith
    have hloglarge :
        Real.log (1 + θ / (c - 1)) > (θ / (c - 1)) / (1 + θ / (c - 1)) := by
      have hpos : 0 < θ / (c - 1) := div_pos hθ0 hcsub
      have hbase : 1 < 1 + θ / (c - 1) := by linarith
      have := Real.log_lt_sub_one_of_pos
        (inv_pos.mpr (by positivity : 0 < 1 + θ / (c - 1)))
        (ne_of_lt ((inv_lt_one₀ (by positivity : 0 < 1 + θ / (c - 1))).2 hbase))
      rw [Real.log_inv] at this
      have hinv : (1 + θ / (c - 1))⁻¹ - 1 =
          -(θ / (c - 1)) / (1 + θ / (c - 1)) := by field_simp <;> ring
      rw [hinv] at this
      have hbound :
          -Real.log (1 + θ / (c - 1)) <
            -((θ / (c - 1)) / (1 + θ / (c - 1))) := by
        simpa [neg_div] using this
      exact (neg_lt_neg_iff.mp hbound)
    have hterm1 :
        (c - 1 + θ) * Real.log (1 + θ / (c - 1)) > θ := by
      have hfac : 0 < c - 1 + θ := by positivity
      have hcancel :
          (c - 1 + θ) * ((θ / (c - 1)) / (1 + θ / (c - 1))) = θ := by
        field_simp
      calc
        θ = (c - 1 + θ) * ((θ / (c - 1)) / (1 + θ / (c - 1))) := hcancel.symm
        _ < (c - 1 + θ) * Real.log (1 + θ / (c - 1)) :=
          mul_lt_mul_of_pos_left hloglarge hfac
    have hstrictCore :
        (c - 1 + θ) * Real.log (1 + θ / (c - 1)) +
            (1 - θ) * Real.log (1 - θ) > 0 := by
      have hmul := mul_lt_mul_of_pos_right hlogsmall hq
      field_simp at hmul
      nlinarith
    have hlogdiff :
        Real.log (c - 1 + θ) = Real.log (c - 1) +
          Real.log (1 + θ / (c - 1)) := by
      have heq : c - 1 + θ = (c - 1) * (1 + θ / (c - 1)) := by
        field_simp
      rw [heq, Real.log_mul hcsub.ne' (by positivity)]
    have hcore :
        c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log (c - 1) > 0 := by
      rw [hEntropy, hlogdiff]
      nlinarith
    have hlogsplit : Real.log ((c - 1) / 9) = Real.log (c - 1) - Real.log 9 := by
      rw [Real.log_div hcsub.ne' (by norm_num : (9 : ℝ) ≠ 0)]
    have hnum :
        c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log 9 >
          θ * Real.log ((c - 1) / 9) := by
      rw [hlogsplit]
      nlinarith
    unfold oldSaving sharpSaving
    exact (div_lt_div_iff_of_pos_right hden).2 (by linarith)

