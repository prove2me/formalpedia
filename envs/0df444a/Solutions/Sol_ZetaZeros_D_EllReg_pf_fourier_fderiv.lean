-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_fourier_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:58.701296+00:00
-- url     : https://prove2.me/submissions/9c42a35d-a30c-47c2-a90f-a208cdc00315

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private theorem fourier_eq_integral_eF_mul (f : E d → ℂ) (ζ : E d) :
    𝓕 f ζ = ∫ x, eF ζ x * f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  try dsimp only
  rw [smul_eq_mul]
  unfold eF
  congr 1; congr 1; push_cast; ring
private theorem contDiff_infty_fderiv_of_contDiff_infty {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.1 hf).2
private theorem differentiable_of_contDiff_infty {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact (contDiff_infty_iff_fderiv.1 hf).1
private theorem exists_clm_eq_neg_two_pi_I_inner (ζ : E d) :
    ∃ L : E d →L[ℝ] ℂ, ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ)) := by
  refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ζ)), fun x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [innerSL_apply_apply, real_inner_comm]; ring
private theorem eF_eq_exp_comp_of_clm (ζ : E d) (L : E d →L[ℝ] ℂ)
    (hL : ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ))) :
    eF ζ = fun x => Complex.exp (L x) := by
  funext x; rw [hL]; rfl
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
set_option maxHeartbeats 800000
namespace ZetaZeros.D.EllReg
theorem _root_.solution (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (v ζ : E d) :
    𝓕 (fun x => fderiv ℝ k x v) ζ = (2 * Real.pi * Complex.I * ((inner ℝ ζ v : ℝ) : ℂ)) * 𝓕 k ζ := by
  obtain ⟨L, hL⟩ := exists_clm_eq_neg_two_pi_I_inner ζ
  have hχ := eF_eq_exp_comp_of_clm ζ L hL
  have hχd : ∀ x, HasFDerivAt (eF ζ) (Complex.exp (L x) • L) x := by
    intro x; rw [hχ]; exact L.hasFDerivAt.cexp
  have hχfd : ∀ x, fderiv ℝ (eF ζ) x v = eF ζ x * L v := by
    intro x
    rw [(hχd x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, hχ]
  have hχc : Continuous (eF ζ) := by rw [hχ]; exact Complex.continuous_exp.comp L.continuous
  have hkd : Differentiable ℝ k := differentiable_of_contDiff_infty hk
  have hχdiff : Differentiable ℝ (eF ζ) := fun x => (hχd x).differentiableAt
  have hDc : Continuous (fun x => fderiv ℝ k x v) := (contDiff_infty_fderiv_of_contDiff_infty hk).continuous.clm_apply continuous_const
  have hDs : HasCompactSupport (fun x => fderiv ℝ k x v) := by
    refine (hkc.fderiv ℝ).mono ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [h0]
    simp
  have i1 : Integrable (fun x => fderiv ℝ (eF ζ) x v * k x) := by
    have e : (fun x => fderiv ℝ (eF ζ) x v * k x) = fun x => eF ζ x * L v * k x := by
      funext x; rw [hχfd]
    rw [e]
    exact ((hχc.mul continuous_const).mul hk.continuous).integrable_of_hasCompactSupport hkc.mul_left
  have i2 : Integrable (fun x => eF ζ x * fderiv ℝ k x v) :=
    (hχc.mul hDc).integrable_of_hasCompactSupport hDs.mul_left
  have i3 : Integrable (fun x => eF ζ x * k x) :=
    (hχc.mul hk.continuous).integrable_of_hasCompactSupport hkc.mul_left
  have hibp : ∫ x, eF ζ x * fderiv ℝ k x v = -∫ x, fderiv ℝ (eF ζ) x v * k x := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hχdiff x) (fun x _ => hkd x)
  rw [fourier_eq_integral_eF_mul, fourier_eq_integral_eF_mul, hibp]
  have e2 : (fun x => fderiv ℝ (eF ζ) x v * k x) = fun x => L v * (eF ζ x * k x) := by
    funext x; rw [hχfd]; ring
  rw [e2, integral_const_mul, hL v, real_inner_comm]
  ring
end ZetaZeros.D.EllReg
