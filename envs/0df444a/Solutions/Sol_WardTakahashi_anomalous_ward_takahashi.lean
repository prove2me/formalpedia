-- Prove2me | solution 1 for WardTakahashi.anomalous_ward_takahashi
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:29:53.734059+00:00
-- url     : https://prove2.me/submissions/4200d1e9-3751-4e23-88ea-eb58f4c951eb

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

set_option autoImplicit false

open MeasureTheory Complex in
theorem WT206_deriv {N : ℕ} (S : WardTakahashi.FieldConfig N → ℝ)
    (F : WardTakahashi.FieldConfig N → ℂ) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F)
    (φ v : WardTakahashi.FieldConfig N) :
    fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ v
      = (fderiv ℝ F φ v - F φ * (fderiv ℝ S φ v : ℂ)) * (Real.exp (-S φ) : ℂ) := by
  have hSd : DifferentiableAt ℝ S φ := (hS.differentiable one_ne_zero) φ
  have hFd : DifferentiableAt ℝ F φ := (hF.differentiable one_ne_zero) φ
  have hE : HasFDerivAt (fun ψ => ((Real.exp (-S ψ) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (Real.exp (-S φ) • (-(fderiv ℝ S φ)))) φ :=
    Complex.ofRealCLM.hasFDerivAt.comp φ (hSd.hasFDerivAt.neg.exp)
  have hG : HasFDerivAt (fun ψ => F ψ * ((Real.exp (-S ψ) : ℝ) : ℂ)) _ φ :=
    hFd.hasFDerivAt.mul hE
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply,
    smul_eq_mul]
  push_cast
  ring

open MeasureTheory Complex in
theorem WT206_contDiffG {N : ℕ} (S : WardTakahashi.FieldConfig N → ℝ)
    (F : WardTakahashi.FieldConfig N → ℂ) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) :=
  hF.mul (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp hS.neg))

open MeasureTheory Complex in
theorem WT206_intG {N : ℕ} (S : WardTakahashi.FieldConfig N → ℝ)
    (F : WardTakahashi.FieldConfig N → ℂ) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F)
    (h0 : Integrable (fun φ : WardTakahashi.FieldConfig N => ‖F φ‖ * Real.exp (-S φ))) :
    Integrable (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) := by
  refine h0.mono' (WT206_contDiffG S F hS hF).continuous.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

open MeasureTheory Complex in
theorem WT206_ibp {N : ℕ} (S : WardTakahashi.FieldConfig N → ℝ)
    (F : WardTakahashi.FieldConfig N → ℂ) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F)
    (h0 : Integrable (fun φ : WardTakahashi.FieldConfig N => ‖F φ‖ * Real.exp (-S φ)))
    (h1 : Integrable (fun φ : WardTakahashi.FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : WardTakahashi.FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖))
    (c : WardTakahashi.FieldConfig N →L[ℝ] ℝ) (v : WardTakahashi.FieldConfig N) :
    Integrable (fun φ => c φ • fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ v) ∧
    ∫ φ, c φ • fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ v
      = -(c v • ∫ φ, F φ * (Real.exp (-S φ) : ℂ)) := by
  set G : WardTakahashi.FieldConfig N → ℂ := fun ψ => F ψ * (Real.exp (-S ψ) : ℂ) with hGdef
  have hGc : ContDiff ℝ 1 G := WT206_contDiffG S F hS hF
  have hGi : Integrable G := WT206_intG S F hS hF h0
  have hGd : Differentiable ℝ G := hGc.differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ G) := hGc.continuous_fderiv one_ne_zero
  have hI1 : Integrable (fun φ => c φ • fderiv ℝ G φ v) := by
    refine (h2.mul_const (‖c‖ * ‖v‖)).mono' ?_ ?_
    · exact (c.continuous.smul ((hdc.clm_apply continuous_const))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [norm_smul]
      calc ‖c x‖ * ‖fderiv ℝ G x v‖ ≤ (‖c‖ * ‖x‖) * (‖fderiv ℝ G x‖ * ‖v‖) :=
            mul_le_mul (c.le_opNorm x) ((fderiv ℝ G x).le_opNorm v) (norm_nonneg _)
              (by positivity)
        _ = ‖x‖ * ‖fderiv ℝ G x‖ * (‖c‖ * ‖v‖) := by ring
  refine ⟨hI1, ?_⟩
  have hI2 : Integrable (fun φ => c φ • G φ) := by
    refine (h1.mul_const ‖c‖).mono' ?_ ?_
    · exact (c.continuous.smul hGc.continuous).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [norm_smul, hGdef]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc ‖c x‖ * (‖F x‖ * Real.exp (-S x)) ≤ (‖c‖ * ‖x‖) * (‖F x‖ * Real.exp (-S x)) :=
            mul_le_mul_of_nonneg_right (c.le_opNorm x) (by positivity)
        _ = ‖x‖ * ‖F x‖ * Real.exp (-S x) * ‖c‖ := by ring
  have hI3 : Integrable (fun φ => fderiv ℝ (⇑c) φ v • G φ) := by
    simp only [ContinuousLinearMap.fderiv]
    exact hGi.smul (c v)
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (WardTakahashi.FieldConfig N))) (f := ⇑c) (g := G) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (by simpa using hI3) (by simpa using hI1)
    (by simpa using hI2) (fun x _ => c.differentiableAt) (fun x _ => hGd x)
  simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.fderiv] at key
  rw [key, integral_smul]

open MeasureTheory Complex in
theorem solution {N : ℕ} (S : WardTakahashi.FieldConfig N → ℝ) (F : WardTakahashi.FieldConfig N → ℂ)
    (A : WardTakahashi.FieldConfig N →L[ℝ] WardTakahashi.FieldConfig N) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F)
    (h0 : Integrable (fun φ : WardTakahashi.FieldConfig N => ‖F φ‖ * Real.exp (-S φ)))
    (h1 : Integrable (fun φ : WardTakahashi.FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : WardTakahashi.FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    ∫ φ, (fderiv ℝ F φ (A φ) - F φ * (fderiv ℝ S φ (A φ) : ℂ)) * (Real.exp (-S φ) : ℂ)
      = -((LinearMap.trace ℝ (WardTakahashi.FieldConfig N) (A : WardTakahashi.FieldConfig N →ₗ[ℝ] WardTakahashi.FieldConfig N) : ℝ) : ℂ)
          * WardTakahashi.pathIntegral S F := by
  set G : WardTakahashi.FieldConfig N → ℂ := fun ψ => F ψ * (Real.exp (-S ψ) : ℂ) with hGdef
  let b := Module.finBasis ℝ (WardTakahashi.FieldConfig N)
  let c : Fin (Module.finrank ℝ (WardTakahashi.FieldConfig N)) →
      WardTakahashi.FieldConfig N →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap ((b.coord i).comp (A : _ →ₗ[ℝ] _))
  have hc : ∀ i φ, c i φ = b.repr (A φ) i := fun i φ => rfl
  have hpt : ∀ φ, (fderiv ℝ F φ (A φ) - F φ * (fderiv ℝ S φ (A φ) : ℂ)) * (Real.exp (-S φ) : ℂ)
      = ∑ i, c i φ • fderiv ℝ G φ (b i) := by
    intro φ
    rw [← WT206_deriv S F hS hF φ (A φ)]
    change fderiv ℝ G φ (A φ) = _
    conv_lhs => rw [← b.sum_repr (A φ)]
    rw [map_sum]
    simp only [map_smul, hc]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun i _ => (WT206_ibp S F hS hF h0 h1 h2 (c i) (b i)).1)]
  simp only [fun i => (WT206_ibp S F hS hF h0 h1 h2 (c i) (b i)).2]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace, WardTakahashi.pathIntegral]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hc, Complex.real_smul]
  push_cast
  rw [Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
