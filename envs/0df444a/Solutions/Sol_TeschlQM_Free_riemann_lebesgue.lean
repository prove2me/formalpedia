-- Prove2me | solution 1 for TeschlQM.Free.riemann_lebesgue
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:56:53.119575+00:00
-- url     : https://prove2.me/submissions/ad489484-b245-496e-9afd-da986288138e

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

open MeasureTheory Filter Topology FourierTransform
open scoped InnerProductSpace SchwartzMap ContDiff

namespace RLAux

theorem fourier_eq_mathlib {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    ∫ x : EuclideanSpace ℝ (Fin n), Complex.exp (-(⟪p, x⟫_ℝ : ℂ) * Complex.I) * f x
      = 𝓕 f ((2 * Real.pi)⁻¹ • p) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  rw [inner_smul_right, real_inner_comm]
  have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

lemma const_pos (n : ℕ) : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity

theorem fourier_eq_scaled {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    TeschlQM.Free.fourier n f p
      = (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ * 𝓕 f ((2 * Real.pi)⁻¹ • p) := by
  unfold TeschlQM.Free.fourier
  rw [fourier_eq_mathlib]

theorem fourier_continuous {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Integrable f volume) :
    Continuous (TeschlQM.Free.fourier n f) := by
  have h1 : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
  have : TeschlQM.Free.fourier n f
      = fun p => (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ * 𝓕 f ((2 * Real.pi)⁻¹ • p) :=
    funext (fourier_eq_scaled f)
  rw [this]
  exact continuous_const.mul (h1.comp (continuous_const_smul _))

theorem fourier_tendsto {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    Tendsto (TeschlQM.Free.fourier n f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  have hne : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
  let h : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) := Homeomorph.smulOfNeZero ((2 * Real.pi)⁻¹ : ℝ) hne
  have h1 : Tendsto (𝓕 f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact f
  have h2 : Tendsto (fun p => 𝓕 f ((2 * Real.pi)⁻¹ • p)) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
    h1.comp h.toCocompactMap.cocompact_tendsto'
  have h3 := h2.const_mul ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹)
  rw [mul_zero] at h3
  have : TeschlQM.Free.fourier n f
      = fun p => (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ * 𝓕 f ((2 * Real.pi)⁻¹ • p) :=
    funext (fourier_eq_scaled f)
  rw [this]
  exact h3

theorem fourier_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    ‖TeschlQM.Free.fourier n f p‖ ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * ∫ x, ‖f x‖ := by
  unfold TeschlQM.Free.fourier
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (const_pos n).le]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (const_pos n).le)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [norm_mul]
  have : ‖Complex.exp (-(⟪p, x⟫_ℝ : ℂ) * Complex.I)‖ = 1 := by
    have := Complex.norm_exp_ofReal_mul_I (-(⟪p, x⟫_ℝ))
    simpa using this
  rw [this, one_mul]


theorem integral_smul_schwartz_eq_zero {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hu : Integrable u volume) (h0 : ∀ w, 𝓕 u w = 0)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : ∫ x, u x • φ x = 0 := by
  set ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := (𝓕⁻ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) with hψ
  have h1 : ∫ ξ, 𝓕 u ξ • ψ ξ = ∫ x, u x • 𝓕 (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ _)
      Real.continuous_fourierChar continuous_inner hu ψ.integrable)
  have h2 : ∀ x, 𝓕 (ψ : EuclideanSpace ℝ (Fin n) → ℂ) x = φ x := by
    intro x
    have h4 : (𝓕 ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) = φ := by
      rw [hψ]
      exact FourierTransform.fourier_fourierInv_eq (E := 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
        (F := 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) φ
    have h3 : ((𝓕 ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : EuclideanSpace ℝ (Fin n) → ℂ)
        = 𝓕 (ψ : EuclideanSpace ℝ (Fin n) → ℂ) := SchwartzMap.fourier_coe ψ
    rw [← h3, h4]
  simp only [h0, zero_smul, integral_zero] at h1
  simp only [h2] at h1
  exact h1.symm

theorem fourier_injective {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume)
    (h : TeschlQM.Free.fourier n f = TeschlQM.Free.fourier n g) : f =ᵐ[volume] g := by
  have hne : ((2 * Real.pi) : ℝ) ≠ 0 := by positivity
  have hcne : ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (const_pos n).ne')
  have hFG : ∀ w, 𝓕 f w = 𝓕 g w := by
    intro w
    have := congrFun h ((2 * Real.pi) • w)
    rw [fourier_eq_scaled, fourier_eq_scaled, smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    exact mul_left_cancel₀ hcne this
  have hu : Integrable (f - g) volume := hf.sub hg
  have h0 : ∀ w, 𝓕 (f - g) w = 0 := by
    intro w
    simp only [Real.fourier_eq, Pi.sub_apply, smul_sub]
    rw [integral_sub ((Real.fourierIntegral_convergent_iff w).2 hf)
      ((Real.fourierIntegral_convergent_iff w).2 hg)]
    have := hFG w
    simp only [Real.fourier_eq] at this
    rw [this, sub_self]
  have hz : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (f - g) x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable ?_
    intro k hk hkc
    have hc : HasCompactSupport (Complex.ofRealCLM ∘ k) := hkc.comp_left (by simp)
    have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ k) := by fun_prop
    have := integral_smul_schwartz_eq_zero (f - g) hu h0 (hc.toSchwartzMap hs)
    simpa [Complex.coe_smul, mul_comm] using this
  filter_upwards [hz] with x hx
  simpa [sub_eq_zero] using hx

end RLAux

/-- Teschl, Lemma 7.6 (Riemann–Lebesgue). -/
theorem solution (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Integrable f volume) :
    Continuous (TeschlQM.Free.fourier n f) ∧
      Tendsto (TeschlQM.Free.fourier n f) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) ∧
      (∀ p, ‖TeschlQM.Free.fourier n f p‖ ≤
        ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * ∫ x, ‖f x‖) ∧
      (∀ g : EuclideanSpace ℝ (Fin n) → ℂ, Integrable g volume →
        TeschlQM.Free.fourier n f = TeschlQM.Free.fourier n g → f =ᵐ[volume] g) :=
  ⟨RLAux.fourier_continuous f hf, RLAux.fourier_tendsto f, RLAux.fourier_bound f,
    fun g hg h => RLAux.fourier_injective f g hf hg h⟩
