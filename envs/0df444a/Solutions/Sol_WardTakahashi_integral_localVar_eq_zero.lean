-- Prove2me | solution 1 for WardTakahashi.integral_localVar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:57:33.94511+00:00
-- url     : https://prove2.me/submissions/b5b27c06-3dfd-4a31-bfc6-29d587d78198

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex WardTakahashi

private theorem integral_coord_smul_fderiv_zero {N : ℕ}
    (G : FieldConfig N → ℂ) (hG : ContDiff ℝ 1 G)
    (u : FieldConfig N →L[ℝ] ℝ) (v : FieldConfig N)
    (huv : u v = 0) (hu : ∀ φ, ‖u φ‖ ≤ ‖φ‖) (hv : ‖v‖ ≤ 1)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖G φ‖))
    (h2 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖fderiv ℝ G φ‖)) :
    Integrable (fun φ : FieldConfig N => u φ • fderiv ℝ G φ v) ∧
      ∫ φ, u φ • fderiv ℝ G φ v = 0 := by
  have hfg : Integrable (fun φ : FieldConfig N => u φ • G φ) := by
    apply Integrable.mono' h1
    · exact (u.continuous.smul hG.continuous).aestronglyMeasurable
    · filter_upwards [] with φ
      simpa [norm_smul] using mul_le_mul_of_nonneg_right (hu φ) (norm_nonneg (G φ))
  have hfg' : Integrable (fun φ : FieldConfig N => u φ • fderiv ℝ G φ v) := by
    apply Integrable.mono' h2
    · exact (u.continuous.smul ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const)).aestronglyMeasurable
    · filter_upwards [] with φ
      calc
        ‖u φ • fderiv ℝ G φ v‖ = ‖u φ‖ * ‖fderiv ℝ G φ v‖ := norm_smul _ _
        _ ≤ ‖u φ‖ * ‖fderiv ℝ G φ‖ := by
          gcongr
          calc
            ‖fderiv ℝ G φ v‖ ≤ ‖fderiv ℝ G φ‖ * ‖v‖ := (fderiv ℝ G φ).le_opNorm v
            _ ≤ ‖fderiv ℝ G φ‖ := by nlinarith [norm_nonneg (fderiv ℝ G φ)]
        _ ≤ ‖φ‖ * ‖fderiv ℝ G φ‖ := by gcongr; exact hu φ
  have hzero : Integrable (fun φ : FieldConfig N => fderiv ℝ (u : FieldConfig N → ℝ) φ v • G φ) := by
    simp [u.fderiv, huv]
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := (volume : Measure (FieldConfig N))) (f := (u : FieldConfig N → ℝ))
    (g := G) (v := v) hzero hfg' hfg
    (fun _ _ => u.differentiableAt) (fun _ _ => hG.differentiable one_ne_zero _)
  exact ⟨hfg', by simpa [u.fderiv, huv] using h⟩

theorem solution {N : ℕ} (G : FieldConfig N → ℂ) (hG : ContDiff ℝ 1 G)
    (x : Fin N)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖G φ‖))
    (h2 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖fderiv ℝ G φ‖)) :
    ∫ φ, localVar x G φ = 0 := by
  let uR : FieldConfig N →L[ℝ] ℝ :=
    Complex.reCLM.comp (ContinuousLinearMap.proj x)
  let uI : FieldConfig N →L[ℝ] ℝ :=
    Complex.imCLM.comp (ContinuousLinearMap.proj x)
  let vR : FieldConfig N := Pi.single x 1
  let vI : FieldConfig N := Pi.single x I
  have hR : Integrable (fun φ : FieldConfig N => uR φ • fderiv ℝ G φ vI) ∧
      ∫ φ, uR φ • fderiv ℝ G φ vI = 0 := by
    apply integral_coord_smul_fderiv_zero G hG uR vI
    · simp [uR, vI]
    · intro φ
      change |(φ x).re| ≤ ‖φ‖
      exact (abs_re_le_norm _).trans (norm_le_pi_norm φ x)
    · simp [vI, Pi.norm_single]
    · exact h1
    · exact h2
  have hI : Integrable (fun φ : FieldConfig N => uI φ • fderiv ℝ G φ vR) ∧
      ∫ φ, uI φ • fderiv ℝ G φ vR = 0 := by
    apply integral_coord_smul_fderiv_zero G hG uI vR
    · simp [uI, vR]
    · intro φ
      change |(φ x).im| ≤ ‖φ‖
      exact (abs_im_le_norm _).trans (norm_le_pi_norm φ x)
    · simp [vR, Pi.norm_single]
    · exact h1
    · exact h2
  have hgen (φ : FieldConfig N) :
      localGen x φ = uR φ • vI - uI φ • vR := by
    ext y
    by_cases hxy : y = x
    · subst y
      simp [localGen, uR, uI, vI, vR, Complex.ext_iff]
    · simp [localGen, uR, uI, vI, vR, hxy]
  have hpoint (φ : FieldConfig N) :
      localVar x G φ = uR φ • fderiv ℝ G φ vI - uI φ • fderiv ℝ G φ vR := by
    simp only [localVar, hgen φ, map_sub, map_smul]
  calc
    ∫ φ, localVar x G φ =
        ∫ φ, uR φ • fderiv ℝ G φ vI - uI φ • fderiv ℝ G φ vR := by
      congr 1
      funext φ
      exact hpoint φ
    _ = 0 := by rw [integral_sub hR.1 hI.1, hR.2, hI.2, sub_self]
