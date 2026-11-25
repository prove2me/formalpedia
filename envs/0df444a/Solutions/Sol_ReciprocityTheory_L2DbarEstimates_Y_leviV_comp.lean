-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviV_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:49.928513+00:00
-- url     : https://prove2.me/submissions/8c299141-a321-4e1a-8010-5c73ad296848

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_wdb_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_eq_dv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
private theorem dv_fderiv_comp_holomorphic {n : ℕ} {h : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hh : DifferentiableAt ℝ h (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dv (fderiv ℝ (h ∘ Φ) v) ζ = dv (fderiv ℝ h (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hh (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dv]
private theorem dv_fderiv_conj_holomorphic_eq_zero {n : ℕ} {c : V n → ℂ} {y : V n} (hc : DifferentiableAt ℂ c y)
    (ζ : V n) : dv (fderiv ℝ (fun v => conj (c v)) y) ζ = 0 := by
  have h := (hc.restrictScalars ℝ).hasFDerivAt.star
  have hL : fderiv ℂ c y (I • ζ) = I * fderiv ℂ c y ζ := by rw [map_smul, smul_eq_mul]
  have hfun : (fun v => conj (c v)) = fun v => star (c v) := rfl
  rw [hfun, h.fderiv, hc.fderiv_restrictScalars ℝ]
  simp only [dv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', hL]
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring
private theorem dv_add' {n : ℕ} (L M : V n →L[ℝ] ℂ) (ζ : V n) :
    dv (L + M) ζ = dv L ζ + dv M ζ := by
  simp only [dv, ContinuousLinearMap.add_apply]
  ring
private theorem dv_sum_smul {n : ℕ} (a : Fin n → ℂ) (L : Fin n → V n →L[ℝ] ℂ) (ζ : V n) :
    dv (∑ k, a k • L k) ζ = ∑ k, a k * dv (L k) ζ := by
  simp only [dv, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {y : V n}
    (hf : ContDiffAt ℝ 2 f (Φ y)) (hΦ : ContDiffAt ℂ 2 Φ y) (ξ : Fin n → ℂ) :
    leviV n (f ∘ Φ) y ξ = leviV n f (Φ y) (fderiv ℂ Φ y (WithLp.toLp 2 ξ)).ofLp := by
  have hΦR : ContDiffAt ℝ 2 Φ y := hΦ.restrict_scalars ℝ
  rw [leviV_eq_dv (hf.comp y hΦR) ξ, leviV_eq_dv hf]
  simp only [WithLp.toLp_ofLp]
  have hfF : DifferentiableAt ℝ (fderiv ℝ f) (Φ y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ k, DifferentiableAt ℝ (wdb n k f) (Φ y) := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (I • bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ f v (bas n k) + I * fderiv ℝ f v (I • bas n k)) (Φ y) :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hΦd : DifferentiableAt ℂ Φ y := hΦ.differentiableAt (by norm_num)
  have hDΦ : DifferentiableAt ℂ (fderiv ℂ Φ) y :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : ∀ k, DifferentiableAt ℂ (fun v => (fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) y := fun k =>
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp y
      (hDΦ.clm_apply (differentiableAt_const _))
  have hev : (fun v => dbv (fderiv ℝ (f ∘ Φ) v) (WithLp.toLp 2 ξ)) =ᶠ[𝓝 y]
      fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) := by
    have h1 : ∀ᶠ v in 𝓝 y, ContDiffAt ℝ 2 f (Φ v) :=
      hΦd.continuousAt.eventually (hf.eventually (by simp))
    have h2 : ∀ᶠ v in 𝓝 y, ContDiffAt ℂ 2 Φ v := hΦ.eventually (by simp)
    filter_upwards [h1, h2] with v hv1 hv2
    rw [dbv_comp (hv1.differentiableAt (by norm_num)) (hv2.differentiableAt (by norm_num)),
      ← sum_wdb_eq]
  have hK : HasFDerivAt
      (fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
      (∑ k, (wdb n k f (Φ y) • fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y +
        conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f ∘ Φ) y)) y := by
    refine HasFDerivAt.fun_sum fun k _ => ?_
    have ha : HasFDerivAt (wdb n k f ∘ Φ) (fderiv ℝ (wdb n k f ∘ Φ) y) y :=
      ((hA k).comp y (hΦd.restrictScalars ℝ)).hasFDerivAt
    have hb : HasFDerivAt (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
        (fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y) y :=
      ((hc k).restrictScalars ℝ).star.hasFDerivAt
    exact ha.mul hb
  have hR : (fun w => dbv (fderiv ℝ f w) (fderiv ℂ Φ y (WithLp.toLp 2 ξ))) =
      fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) := by
    funext w
    rw [← sum_wdb_eq]
  have hRD : HasFDerivAt (fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k))
      (∑ k, conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f) (Φ y)) (Φ y) :=
    HasFDerivAt.fun_sum fun k _ => (hA k).hasFDerivAt.mul_const _
  rw [hev.fderiv_eq, hK.fderiv, hR, hRD.fderiv, Finset.sum_add_distrib, dv_add', dv_sum_smul,
    dv_sum_smul, dv_sum_smul]
  simp only [dv_fderiv_conj_holomorphic_eq_zero (hc _), mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dv_fderiv_comp_holomorphic (hA k) hΦd]
end ReciprocityTheory.L2DbarEstimates.Y
