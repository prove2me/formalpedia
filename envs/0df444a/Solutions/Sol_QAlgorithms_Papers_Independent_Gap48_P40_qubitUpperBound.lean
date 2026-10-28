-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.qubitUpperBound
-- status  : ACCEPTED   (disprove)
-- author  : @Alien60
-- created : 2026-10-27T00:13:53.190511+00:00
-- url     : https://prove2.me/submissions/3ab3ef9f-79b0-4eed-aa89-be7b12f7f264

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40.Disproof

/-- The counterexample state `ρ = |+⟩⟨+|`. -/
def cxRho : Mat 2 := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- The counterexample reference `σ = diag(1/8, 7/8)`. -/
def cxSigma : Mat 2 := !![1 / 8, 0; 0, 7 / 8]

/-- The L2 operator norm is unitarily invariant. -/
theorem opNorm_isUINorm : IsUINorm (fun A : Mat 2 => ‖A‖) := by
  refine ⟨fun A => norm_nonneg A, fun A => norm_eq_zero, fun A B => norm_add_le A B,
    fun c A => norm_smul c A, ?_⟩
  intro U V A
  simp only
  rw [CStarRing.norm_mul_mem_unitary _ V.2, CStarRing.norm_mem_unitary_mul _ U.2]

/-- In a C⋆-ring, `star H * H = c • 1` with `c ≥ 0` forces `‖H‖ = √c`. -/
theorem norm_of_star_mul_self {H : Mat 2} {c : ℝ} (hc : 0 ≤ c)
    (h : star H * H = (c : ℂ) • (1 : Mat 2)) : ‖H‖ = Real.sqrt c := by
  have h1 : ‖H‖ * ‖H‖ = c := by
    rw [← CStarRing.norm_star_mul_self, h, norm_smul, norm_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hc]
  rw [← h1, Real.sqrt_mul_self (norm_nonneg _)]

/-- If `x` is in the real spectrum of a `2 × 2` matrix, then `det (x • 1 - A) = 0`. -/
theorem det_eq_zero_of_mem_spectrum {A : Mat 2} {x : ℝ} (hx : x ∈ spectrum ℝ A) :
    (x • (1 : Mat 2) - A).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one] at hx
  exact hx

theorem spectrum_rho {x : ℝ} (hx : x ∈ spectrum ℝ cxRho) : x = 0 ∨ x = 1 := by
  have h := det_eq_zero_of_mem_spectrum hx
  rw [Matrix.det_fin_two] at h
  simp [cxRho, Matrix.smul_apply, Matrix.one_apply] at h
  have h' : ((x * (x - 1) : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
  have h'' : x * (x - 1) = 0 := by exact_mod_cast h'
  rcases mul_eq_zero.mp h'' with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

theorem spectrum_sigma {x : ℝ} (hx : x ∈ spectrum ℝ cxSigma) : x = 1 / 8 ∨ x = 7 / 8 := by
  have h := det_eq_zero_of_mem_spectrum hx
  rw [Matrix.det_fin_two] at h
  simp [cxSigma, Matrix.smul_apply] at h
  rcases h with h | h
  · left; have := congrArg Complex.re h; simp at this; linarith
  · right; have := congrArg Complex.re h; simp at this; linarith

theorem rho_herm : cxRho.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxRho, Matrix.conjTranspose_apply]

theorem sigma_herm : cxSigma.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxSigma, Matrix.conjTranspose_apply]

theorem rho_density : IsDensityMatrix cxRho := by
  refine ⟨?_, ?_⟩
  · have h : cxRho * cxRho = cxRho := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [cxRho, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    have h2 := Matrix.posSemidef_conjTranspose_mul_self cxRho
    rwa [rho_herm.eq, h] at h2
  · simp [cxRho, Matrix.trace_fin_two]; norm_num

theorem sigma_eq_diag : cxSigma = Matrix.diagonal ![(1 / 8 : ℂ), 7 / 8] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxSigma]

theorem sigma_density : IsDensityMatrix cxSigma := by
  refine ⟨?_, ?_⟩
  · rw [sigma_eq_diag, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp
    rw [show (7 / 8 : ℂ) = ((7 / 8 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  · simp [cxSigma, Matrix.trace_fin_two]; norm_num

theorem rev_zero_max {m : ℕ} (hm : 0 < m) (k : Fin m) : k ≤ Fin.rev ⟨0, hm⟩ := by
  rw [Fin.le_def, Fin.val_rev]
  have := k.isLt
  have h0 : ((⟨0, hm⟩ : Fin m) : ℕ) = 0 := rfl
  omega

/-- The minimal eigenvalue of `σ` is `1/8`. -/
theorem minEigenvalue_sigma : minEigenvalue cxSigma = 1 / 8 := by
  classical
  set h := sigma_herm
  have hcard : 0 < Fintype.card (Fin 2) := by simp
  have hmin : minEigenvalue cxSigma = h.eigenvalues₀ (Fin.rev ⟨0, hcard⟩) := by
    simp [minEigenvalue, ascEigenvalues, h, hcard]
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))
  -- the minimal eigenvalue is an eigenvalue, hence in the spectrum
  have hmem : h.eigenvalues₀ (Fin.rev ⟨0, hcard⟩) ∈ spectrum ℝ cxSigma := by
    have := h.eigenvalues_mem_spectrum_real (e (Fin.rev ⟨0, hcard⟩))
    unfold Matrix.IsHermitian.eigenvalues at this
    erw [Equiv.symm_apply_apply] at this
    exact this
  -- every eigenvalue dominates it
  have hge : ∀ i, h.eigenvalues₀ (Fin.rev ⟨0, hcard⟩) ≤ h.eigenvalues i := by
    intro i
    exact h.eigenvalues₀_antitone (rev_zero_max hcard _)
  -- the eigenvalues sum to the trace, which is 1
  have htr : ∑ i, h.eigenvalues i = 1 := by
    have := congrArg Complex.re h.trace_eq_sum_eigenvalues
    rw [show (cxSigma.trace).re = 1 by simp [cxSigma, Matrix.trace_fin_two]; norm_num] at this
    simpa [Complex.re_sum] using this.symm
  rw [hmin]
  rcases spectrum_sigma hmem with h1 | h1
  · exact h1
  · exfalso
    have : ∑ i : Fin 2, (7 / 8 : ℝ) ≤ ∑ i, h.eigenvalues i :=
      Finset.sum_le_sum fun i _ => h1 ▸ hge i
    simp at this
    rw [Fin.sum_univ_two] at htr
    linarith

theorem rescaled_value :
    rescaled (fun A : Mat 2 => ‖A‖) (cxRho - cxSigma) = 5 / 8 := by
  have hH : ‖cxRho - cxSigma‖ = 5 / 8 := by
    rw [norm_of_star_mul_self (c := 25 / 64) (by norm_num)]
    · rw [show (25 / 64 : ℝ) = (5 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    · rw [Matrix.star_eq_conjTranspose, (rho_herm.sub sigma_herm).eq]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [cxRho, cxSigma, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
  have hF : ‖matrixF 2‖ = 1 := by
    rw [norm_of_star_mul_self (c := 1) (by norm_num), Real.sqrt_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [matrixF, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  simp only [rescaled, hH, hF, div_one]

/-- `log σ = a • 1 + b • σ` for the affine interpolant through `(1/8, log 1/8)` and
`(7/8, log 7/8)`. -/
theorem cfc_log_sigma :
    cfc Real.log cxSigma =
      algebraMap ℝ (Mat 2) (Real.log (1 / 8) - (Real.log (7 / 8) - Real.log (1 / 8)) / 6) +
        ((4 / 3) * (Real.log (7 / 8) - Real.log (1 / 8))) • cxSigma := by
  have hsa : IsSelfAdjoint cxSigma := sigma_herm
  set a0 := Real.log (1 / 8) - (Real.log (7 / 8) - Real.log (1 / 8)) / 6
  set b0 := (4 / 3) * (Real.log (7 / 8) - Real.log (1 / 8))
  rw [cfc_congr (g := fun x => (fun _ => a0) x + (fun x => b0 * x) x)]
  · rw [cfc_add (a := cxSigma) (fun _ => a0) (fun x => b0 * x) continuousOn_const
      ((continuous_const.mul continuous_id).continuousOn),
      cfc_const (ha := hsa), cfc_const_mul_id (ha := hsa)]
  · intro x hx
    rcases spectrum_sigma hx with rfl | rfl <;> simp only [a0, b0] <;> ring

theorem cfc_xlogx_rho : cfc (fun x : ℝ => x * Real.log x) cxRho = 0 := by
  rw [cfc_congr (g := 0), cfc_zero]
  intro x hx
  rcases spectrum_rho hx with rfl | rfl <;> simp

theorem isSupported : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported cxRho cxSigma := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [cxSigma, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hv0 : v = 0 := by
    ext i; fin_cases i <;> simp [h0, h1]
  rw [hv0, Matrix.mulVec_zero]

theorem relativeEntropy_value :
    relativeEntropy cxRho cxSigma =
      ((-(Real.log (1 / 8) + Real.log (7 / 8)) / 2 : ℝ) : EReal) := by
  rw [relativeEntropy, if_pos isSupported, cfc_xlogx_rho, cfc_log_sigma]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [Matrix.trace_fin_two, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply]
  simp [cxRho, cxSigma, Complex.log_re]
  ring

theorem bound_lt :
    qubitLargeBound (1 / 8) (5 / 8) < (-(Real.log (1 / 8) + Real.log (7 / 8)) / 2) := by
  have l2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have e8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have e78 : Real.log (7 / 8) = Real.log 7 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]; push_cast; ring
  have e38 : Real.log (1 - 5 / 8) = Real.log 3 - 3 * Real.log 2 := by
    rw [show (1 - 5 / 8 : ℝ) = 3 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have e6 : Real.log (1 + 5 / 8 / (1 / 8)) = Real.log 2 + Real.log 3 := by
    rw [show (1 + 5 / 8 / (1 / 8) : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have e27 : Real.log (1 - 5 / 8 / (1 - 1 / 8)) = Real.log 2 - Real.log 7 := by
    rw [show (1 - 5 / 8 / (1 - 1 / 8) : ℝ) = 2 / 7 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  -- log 7 < log 9 = 2 log 3
  have h79 : Real.log 7 < 2 * Real.log 3 := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) < 3 ^ 2)
    rw [Real.log_pow] at this
    push_cast at this; linarith
  -- log 189 < log 256, i.e. 3 log 3 + log 7 < 8 log 2
  have h189 : 3 * Real.log 3 + Real.log 7 < 8 * Real.log 2 := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 ^ 3 * 7) (by norm_num : (3 : ℝ) ^ 3 * 7 < 2 ^ 8)
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow] at this
    push_cast at this; linarith
  unfold qubitLargeBound
  rw [e38, e6, e27, e8, e78]
  apply max_lt
  · linarith
  · norm_num; nlinarith

end QAlgorithms.Papers.Independent.Gap48.P40.Disproof

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution : ¬ (∀ (N : Mat 2 → ℝ) (hN : IsUINorm N) (rho sigma : Mat 2)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma),
    let beta := minEigenvalue sigma
    let T := rescaled N (rho - sigma)
    (T ≤ beta → relativeEntropy rho sigma ≤ ((qubitSmallBound beta T : ℝ) : EReal)) ∧
    (beta < T → relativeEntropy rho sigma ≤ ((qubitLargeBound beta T : ℝ) : EReal))) := by
  open QAlgorithms.Papers.Independent.Gap48.P40.Disproof in
  intro h
  have hb : 0 < minEigenvalue cxSigma := by rw [minEigenvalue_sigma]; norm_num
  have h2 := (h _ opNorm_isUINorm cxRho cxSigma rho_density sigma_density hb).2
  simp only [minEigenvalue_sigma, rescaled_value] at h2
  have h3 := h2 (by norm_num)
  rw [relativeEntropy_value, EReal.coe_le_coe_iff] at h3
  exact absurd h3 (not_le.mpr bound_lt)
