-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGramMA_proof_e3fb81211f72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:51.187618+00:00
-- url     : https://prove2.me/submissions/fead5a65-b1e3-4e91-87fd-5f500ecc41db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramPolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartGramMA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_det_eq_corner_mul_schur_1edb5dadec12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity cxHessian)
namespace GroundTheory.Heights₂.Heights
namespace ChartGramMA
theorem _root_.solution : ChartGramMA.Statement := by
  intro e n v y hv h0

  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hv
  have han : AnalyticOnNhd ℂ v t := by
    have hd : DifferentiableOn ℂ v t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL
  set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def
  have hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y' := by
    filter_upwards [hto.mem_nhds hyt] with y' hy'
    exact (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')
  have hu0 : u y ≠ 0 := by
    simpa [hu_def, hL, PiLp.coe_symm_continuousLinearEquiv] using h0
  have hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b) := fun b => by
    have hc := (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y
      (hv.self_of_nhds).hasFDerivAt
    have hc' : HasFDerivAt u _ y := hc
    rw [hc'.fderiv]
    rfl

  have hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) =
      fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re := by
    funext _ y'
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (u y')
    have h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2 := h
    rw [h', Real.log_pow]
    simp [hu_def, hL]

  set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) :=
    Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw
  set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def
  have hmat : G = Matrix.of fun a b => ∑ i,
      star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) *
        (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i := by
    ext a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>
      simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>
      simp [hu_def, hL]
  have hgram : gramVol v y = G.det.re := by
    rw [hmat]; rfl
  have hG00 : G 0 0 ≠ 0 := by
    simpa [hG_def, hw] using hu0
  have hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y =
      (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e =>
        G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) := by
    ext i j
    rw [ChartGram.cxHessian_half_log hu hu0]
    simp only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
    have : ⟪u y, u y⟫_ℂ ≠ 0 := by simpa [hG_def, hw] using hG00
    field_simp
  have hS := ChartGram.det_eq_corner_mul_schur G hG00
  have hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG_def, hw]
  have hNpos : 0 < ‖u y‖ := norm_pos_iff.2 hu0
  unfold maDensity
  rw [hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    hgram, hS]
  generalize (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z
  rw [hN]
  have hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖ := rfl
  rw [hnorm]
  generalize ‖u y‖ = r at hNpos ⊢
  rw [show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]
  have hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  have hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  have h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  linear_combination (r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi +
    (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2
end ChartGramMA
end GroundTheory.Heights₂.Heights
