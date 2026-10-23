-- Prove2me | solution 1 for RiskFunctionals.Frontier.capm_beta_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:27:47.680641+00:00
-- url     : https://prove2.me/submissions/801dd2e4-8a27-4cd9-9393-20bdbaa7534e

import Mathlib
import Definitions.Def_RiskFunctionals_Frontier_MeanVariance

open MeasureTheory ProbabilityTheory Matrix RiskFunctionals.Frontier

section g79m
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}
  {ξ : Fin M → Ω → ℝ}

lemma g79m_memLp (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    MemLp (fun ω => c + ∑ m, a m * ξ m ω) 2 P := by
  have h1 : MemLp (fun ω => ∑ m, a m * ξ m ω) 2 P := by
    have := memLp_finsetSum' (μ := P) (p := 2) Finset.univ (fun m _ => (hξ m).const_mul (a m))
    convert this using 1; ext ω; simp [Finset.sum_apply]
  exact (memLp_const c).add h1

lemma g79m_mean (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    ∫ ω, (c + ∑ m, a m * ξ m ω) ∂P = c + a ⬝ᵥ meanVector P ξ := by
  have hi : ∀ m, Integrable (fun ω => a m * ξ m ω) P :=
    fun m => ((hξ m).integrable (by norm_num)).const_mul (a m)
  rw [integral_add (integrable_const c) (integrable_finset_sum _ (fun m _ => hi m)),
    integral_finset_sum _ (fun m _ => hi m)]
  simp [dotProduct, meanVector, integral_const_mul]

lemma g79m_cov (hξ : ∀ m, MemLp (ξ m) 2 P) (c d : ℝ) (a b : Fin M → ℝ) :
    covariance (fun ω => c + ∑ m, a m * ξ m ω) (fun ω => d + ∑ m, b m * ξ m ω) P =
      a ⬝ᵥ covMatrix P ξ *ᵥ b := by
  have hA : ∀ (a : Fin M → ℝ), MemLp (fun ω => ∑ m, a m * ξ m ω) 2 P := by
    intro a; simpa using g79m_memLp hξ 0 a
  rw [covariance_const_add_left ((hA a).integrable (by norm_num)),
    covariance_const_add_right ((hA b).integrable (by norm_num)),
    covariance_fun_sum_fun_sum (fun m => (hξ m).const_mul (a m)) (fun m => (hξ m).const_mul (b m))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, dotProduct, mulVec,
    covMatrix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma g79m_var (hξ : ∀ m, MemLp (ξ m) 2 P) (c : ℝ) (a : Fin M → ℝ) :
    variance (fun ω => c + ∑ m, a m * ξ m ω) P = a ⬝ᵥ covMatrix P ξ *ᵥ a := by
  rw [← covariance_self (g79m_memLp hξ c a).aemeasurable, g79m_cov hξ]

lemma g79m_symm : (covMatrix P ξ)ᵀ = covMatrix P ξ := by
  ext i j; simp [covMatrix, covariance_comm]

lemma g79m_psd (hξ : ∀ m, MemLp (ξ m) 2 P) : (covMatrix P ξ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simpa [Matrix.IsHermitian] using g79m_symm (P := P) (ξ := ξ)
  · have := g79m_var hξ 0 x
    simp only [star_trivial]
    rw [← this]; exact variance_nonneg _ _

lemma g79m_posDef (hξ : ∀ m, MemLp (ξ m) 2 P) (hC : IsUnit (covMatrix P ξ)) :
    (covMatrix P ξ).PosDef := (g79m_psd hξ).posDef_iff_isUnit.mpr hC

lemma g79m_inv_pos (hξ : ∀ m, MemLp (ξ m) 2 P) (hC : IsUnit (covMatrix P ξ))
    {v : Fin M → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ v := by
  have h := ((g79m_posDef hξ hC).inv)
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv
  simpa using this

lemma g79m_mul_inv (hC : IsUnit (covMatrix P ξ)) (v : Fin M → ℝ) :
    covMatrix P ξ *ᵥ ((covMatrix P ξ)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hC), one_mulVec]

lemma g79m_inv_symm (v w : Fin M → ℝ) :
    v ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ w = w ⬝ᵥ (covMatrix P ξ)⁻¹ *ᵥ v := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, Matrix.transpose_nonsing_inv,
    g79m_symm]

/-- quadratic form symmetric: `a ⬝ C b = b ⬝ C a` -/
lemma g79m_C_symm (a b : Fin M → ℝ) :
    a ⬝ᵥ covMatrix P ξ *ᵥ b = b ⬝ᵥ covMatrix P ξ *ᵥ a := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, g79m_symm]

end g79m


lemma g79m_pr {Ω : Type*} {M : ℕ} (ξ : Fin M → Ω → ℝ) (x : Fin M → ℝ) :
    portfolioReturn ξ x = fun ω => 0 + ∑ m, x m * ξ m ω := by
  funext ω; simp [portfolioReturn]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (r₀ : ℝ) (hC : IsUnit (covMatrix P ξ)) (hq : meanVector P ξ ≠ fun _ => r₀) :
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let v := r - r₀ • one
    let xplus : Fin M → ℝ := (1 / (one ⬝ᵥ C⁻¹ *ᵥ v)) • C⁻¹ *ᵥ v
    let Yplus : Ω → ℝ := portfolioReturn ξ xplus
    let μplus : ℝ := ∫ ω, Yplus ω ∂P
    one ⬝ᵥ C⁻¹ *ᵥ v ≠ 0 →
    ∀ (x₀ : ℝ) (x : Fin M → ℝ), one ⬝ᵥ x + x₀ = 1 →
      ∫ ω, riskFreeReturn r₀ ξ x₀ x ω ∂P =
        r₀ + (covariance (riskFreeReturn r₀ ξ x₀ x) Yplus P / variance Yplus P) * (μplus - r₀) := by
  intro C r one v xplus Yplus μplus hs x₀ x hx
  have hv : v ≠ 0 := by
    intro h; apply hq; funext m; have := congrFun h m
    simp [v, one, r] at this; linarith
  have hq0 := g79m_inv_pos hξ hC hv
  set w := C⁻¹ *ᵥ v with hw
  set s := one ⬝ᵥ w with hs'
  have hCw : C *ᵥ w = v := g79m_mul_inv hC v
  have hY : Yplus = fun ω => 0 + ∑ m, xplus m * ξ m ω := g79m_pr ξ xplus
  have hR : riskFreeReturn r₀ ξ x₀ x = fun ω => x₀ * r₀ + ∑ m, x m * ξ m ω := rfl
  have hμ : μplus = (1 / s) * (r ⬝ᵥ w) := by
    show ∫ ω, Yplus ω ∂P = _
    rw [hY, g79m_mean hξ]; simp [xplus, r, dotProduct_comm]; rfl
  have hcov : covariance (riskFreeReturn r₀ ξ x₀ x) Yplus P = (1 / s) * (x ⬝ᵥ v) := by
    rw [hR, hY, g79m_cov hξ]
    show x ⬝ᵥ C *ᵥ ((1 / s) • w) = _
    rw [mulVec_smul, hCw, dotProduct_smul, smul_eq_mul]
  have hvar : variance Yplus P = (1 / s) ^ 2 * (v ⬝ᵥ w) := by
    rw [hY, g79m_var hξ]
    show ((1 / s) • w) ⬝ᵥ C *ᵥ ((1 / s) • w) = _
    rw [mulVec_smul, hCw, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      dotProduct_comm w v]; ring
  have hmean : ∫ ω, riskFreeReturn r₀ ξ x₀ x ω ∂P = x₀ * r₀ + x ⬝ᵥ r := by
    rw [hR, g79m_mean hξ]
  have hvw : v ⬝ᵥ w = r ⬝ᵥ w - r₀ * s := by
    simp [v, sub_dotProduct, smul_dotProduct, s]
  have hxv : x ⬝ᵥ v = x ⬝ᵥ r - r₀ * (1 - x₀) := by
    have : one ⬝ᵥ x = x ⬝ᵥ one := dotProduct_comm _ _
    simp only [v, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [← this, ← hx]; ring
  rw [hmean, hcov, hvar, hμ]
  have hq0' : 0 < v ⬝ᵥ w := hq0
  field_simp
  rw [hxv]
  have : r ⬝ᵥ w = v ⬝ᵥ w + r₀ * s := by linarith
  rw [this]; field_simp; ring
