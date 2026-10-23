-- Prove2me | solution 1 for RiskFunctionals.Frontier.capm_variance_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:31:19.557477+00:00
-- url     : https://prove2.me/submissions/4a659b02-ec05-4601-b958-5ca4997145a1

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


noncomputable def g79m_P : Measure Bool := (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

instance g79m_inst : IsProbabilityMeasure g79m_P := ⟨by
  simp [g79m_P]; rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num⟩

def g79m_xi : Fin 1 → Bool → ℝ := fun _ b => if b then 1 else -1

lemma g79m_int (f : Bool → ℝ) : ∫ b, f b ∂g79m_P = (f true + f false) / 2 := by
  rw [g79m_P, integral_smul_measure, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
  simp [integral_dirac]; ring

lemma g79m_mean0 : meanVector g79m_P g79m_xi = 0 := by
  funext m; simp [meanVector, g79m_int, g79m_xi]

lemma g79m_cov1 : covMatrix g79m_P g79m_xi = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [covMatrix, covariance, g79m_int, g79m_xi]

lemma g79m_mlx : ∀ m, MemLp (g79m_xi m) 2 g79m_P := by
  intro m
  exact MemLp.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun b => by
    cases b <;> simp [g79m_xi])

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : ℕ} (ξ : Fin M → Ω → ℝ) (hξ : ∀ m, MemLp (ξ m) 2 P)
    (r₀ : ℝ) (hC : IsUnit (covMatrix P ξ)) (hq : meanVector P ξ ≠ fun _ => r₀),
    let C := covMatrix P ξ
    let r := meanVector P ξ
    let one : Fin M → ℝ := fun _ => 1
    let v := r - r₀ • one
    let xplus : Fin M → ℝ := (1 / (one ⬝ᵥ C⁻¹ *ᵥ v)) • C⁻¹ *ᵥ v
    let Yplus : Ω → ℝ := portfolioReturn ξ xplus
    let μplus : ℝ := ∫ ω, Yplus ω ∂P
    let σplus2 : ℝ := variance Yplus P
    one ⬝ᵥ C⁻¹ *ᵥ v ≠ 0 →
    ∀ (x₀ : ℝ) (x : Fin M → ℝ), one ⬝ᵥ x + x₀ = 1 →
      let Yx : Ω → ℝ := riskFreeReturn r₀ ξ x₀ x
      let bound : ℝ := ((∫ ω, Yx ω ∂P - r₀) / (μplus - r₀)) ^ 2 * σplus2
      bound ≤ variance Yx P ∧
      (variance Yx P = bound ↔ ∃ μ : ℝ, IsSolution423 C r r₀ μ x₀ x) ∧
      (0 < variance Yx P → (variance Yx P = bound ↔ correlation P Yx Yplus = 1))) := by
  intro h
  have hC : IsUnit (covMatrix g79m_P g79m_xi) := by rw [g79m_cov1]; exact isUnit_one
  have hq : meanVector g79m_P g79m_xi ≠ fun _ => (-1 : ℝ) := by
    rw [g79m_mean0]; intro h'; have := congrFun h' 0; simp at this
  have H := h g79m_P g79m_xi g79m_mlx (-1) hC hq
  simp only [g79m_cov1, g79m_mean0, inv_one, one_mulVec] at H
  have hs : (fun _ => (1:ℝ)) ⬝ᵥ ((0 : Fin 1 → ℝ) - (-1 : ℝ) • fun _ => (1:ℝ)) ≠ 0 := by
    simp [dotProduct]
  have H2 := (H hs 2 (fun _ => -1) (by simp [dotProduct]; norm_num)).2.2
  -- compute everything
  have hxp : ((1 / (fun _ => (1:ℝ)) ⬝ᵥ ((0 : Fin 1 → ℝ) - (-1 : ℝ) • fun _ => (1:ℝ))) •
      ((0 : Fin 1 → ℝ) - (-1 : ℝ) • fun _ => (1:ℝ))) = fun _ => 1 := by
    funext i; simp [dotProduct]
  rw [hxp] at H2
  have hpr : portfolioReturn g79m_xi (fun _ => (1:ℝ)) = fun ω => 0 + ∑ m, (fun _ => (1:ℝ)) m * g79m_xi m ω := by
    funext ω; simp [portfolioReturn]
  have hrf : riskFreeReturn (-1) g79m_xi 2 (fun _ => (-1:ℝ)) =
      fun ω => 2 * (-1) + ∑ m, (fun _ => (-1:ℝ)) m * g79m_xi m ω := rfl
  rw [hpr, hrf, correlation, g79m_var g79m_mlx, g79m_var g79m_mlx, g79m_cov g79m_mlx,
    g79m_mean g79m_mlx, g79m_mean g79m_mlx, g79m_cov1, g79m_mean0] at H2
  norm_num [dotProduct] at H2
