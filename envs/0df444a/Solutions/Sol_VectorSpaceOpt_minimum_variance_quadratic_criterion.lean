-- Prove2me | solution 1 for VectorSpaceOpt.minimum_variance_quadratic_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T14:02:37.212811+00:00
-- url     : https://prove2.me/submissions/030adcab-ecb8-43dd-9480-196c97146e8a

import Mathlib
open Matrix MeasureTheory

section Moments
variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A product of two linear forms in `y` is a double sum of the entrywise products. -/
theorem vsm_quad_point (y : Ω → Fin m → ℝ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) (ω : Ω) :
    A.mulVec (y ω) i * B.mulVec (y ω) j
      = ∑ k, ∑ l, (A i k * B j l) * (y ω k * y ω l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem vsm_cross_point (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) (ω : Ω) :
    b ω i * K.mulVec (y ω) j = ∑ l, K j l * (b ω i * y ω l) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem vsm_int_quad (y : Ω → Fin m → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    Integrable (fun ω => A.mulVec (y ω) i * B.mulVec (y ω) j) μ := by
  refine Integrable.congr (f := fun ω => ∑ k, ∑ l, (A i k * B j l) * (y ω k * y ω l)) ?_ ?_
  · apply integrable_finset_sum
    intro k _
    apply integrable_finset_sum
    intro l _
    exact (hyy k l).const_mul _
  · exact Filter.Eventually.of_forall fun ω => (vsm_quad_point y A B i j ω).symm

theorem vsm_int_cross (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    Integrable (fun ω => b ω i * K.mulVec (y ω) j) μ := by
  refine Integrable.congr (f := fun ω => ∑ l, K j l * (b ω i * y ω l)) ?_ ?_
  · apply integrable_finset_sum
    intro l _
    exact (hby i l).const_mul _
  · exact Filter.Eventually.of_forall fun ω => (vsm_cross_point y b K i j ω).symm

theorem vsm_quad_int (y : Ω → Fin m → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, A.mulVec (y ω) i * B.mulVec (y ω) j ∂μ = (A * Syy * Bᵀ) i j := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall (vsm_quad_point y A B i j))]
  rw [integral_finset_sum _ (fun k _ => by
    apply integrable_finset_sum; intro l _; exact (hyy k l).const_mul _)]
  have hk : ∀ k ∈ Finset.univ,
      (∫ ω, (∑ l, (A i k * B j l) * (y ω k * y ω l)) ∂μ)
        = ∑ l, (A i k * B j l) * Syy k l := by
    intro k _
    rw [integral_finset_sum _ (fun l _ => (hyy k l).const_mul _)]
    exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul, hSyy k l]
  rw [Finset.sum_congr rfl hk]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vsm_cross_int (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, b ω i * K.mulVec (y ω) j ∂μ = (Sby * Kᵀ) i j := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall (vsm_cross_point y b K i j))]
  rw [integral_finset_sum _ (fun l _ => (hby i l).const_mul _)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul, hSby i l]; ring

/-- The error covariance of a linear estimate, in terms of second moments. -/
theorem vsm_err_cov (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (hbb : ∀ i j : Fin n, Integrable (fun ω => b ω i * b ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (Sbb : Matrix (Fin n) (Fin n) ℝ) (hSbb : ∀ i j, ∫ ω, b ω i * b ω j ∂μ = Sbb i j)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, (b ω i - K.mulVec (y ω) i) * (b ω j - K.mulVec (y ω) j) ∂μ
      = Sbb i j - (Sby * Kᵀ) i j - (K * Sbyᵀ) i j + (K * Syy * Kᵀ) i j := by
  classical
  have hpoint : ∀ ω, (b ω i - K.mulVec (y ω) i) * (b ω j - K.mulVec (y ω) j)
      = b ω i * b ω j - b ω i * K.mulVec (y ω) j
        - b ω j * K.mulVec (y ω) i + K.mulVec (y ω) i * K.mulVec (y ω) j := by
    intro ω; ring
  have i1 : Integrable (fun ω => b ω i * b ω j) μ := hbb i j
  have i2 : Integrable (fun ω => b ω i * K.mulVec (y ω) j) μ := vsm_int_cross μ y b hby K i j
  have i3 : Integrable (fun ω => b ω j * K.mulVec (y ω) i) μ := vsm_int_cross μ y b hby K j i
  have i4 : Integrable (fun ω => K.mulVec (y ω) i * K.mulVec (y ω) j) μ :=
    vsm_int_quad μ y hyy K K i j
  have i12 : Integrable (fun ω => b ω i * b ω j - b ω i * K.mulVec (y ω) j) μ := i1.sub i2
  have i123 : Integrable (fun ω => b ω i * b ω j - b ω i * K.mulVec (y ω) j
      - b ω j * K.mulVec (y ω) i) μ := i12.sub i3
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  rw [hSbb i j, vsm_cross_int μ y b hby Sby hSby K i j,
    vsm_cross_int μ y b hby Sby hSby K j i, vsm_quad_int μ y hyy Syy hSyy K K i j]
  have hsymm : (Sby * Kᵀ) j i = (K * Sbyᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hsymm]

end Moments


theorem solution {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (β : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hβy : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * y ω j) μ)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sβy : Matrix (Fin n) (Fin m) ℝ) (hSβy : ∀ i j, ∫ ω, β ω i * y ω j ∂μ = Sβy i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sβy * Syy⁻¹)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    ∫ ω, (∑ i, ∑ j, (β ω i - K₀.mulVec (y ω) i) * P i j *
            (β ω j - K₀.mulVec (y ω) j)) ∂μ ≤
    ∫ ω, (∑ i, ∑ j, (β ω i - K.mulVec (y ω) i) * P i j *
            (β ω j - K.mulVec (y ω) j)) ∂μ := by
  classical
  set Sββ : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ∫ ω, β ω i * β ω j ∂μ with hSββdef
  have hSββ : ∀ i j, ∫ ω, β ω i * β ω j ∂μ = Sββ i j := fun i j => rfl
  -- the integral of the quadratic criterion is the `P`-pairing of the error covariance
  have hcrit : ∀ A : Matrix (Fin n) (Fin m) ℝ,
      ∫ ω, (∑ i, ∑ j, (β ω i - A.mulVec (y ω) i) * P i j *
              (β ω j - A.mulVec (y ω) j)) ∂μ
        = ∑ i, ∑ j, P i j *
            (Sββ - Sβy * Aᵀ - A * Sβyᵀ + A * Syy * Aᵀ) i j := by
    intro A
    have hint : ∀ i j : Fin n,
        Integrable (fun ω => (β ω i - A.mulVec (y ω) i) * P i j *
          (β ω j - A.mulVec (y ω) j)) μ := by
      intro i j
      have h1 : Integrable (fun ω => (β ω i - A.mulVec (y ω) i) *
          (β ω j - A.mulVec (y ω) j)) μ := by
        have e : (fun ω => (β ω i - A.mulVec (y ω) i) * (β ω j - A.mulVec (y ω) j))
            = (fun ω => β ω i * β ω j - β ω i * A.mulVec (y ω) j
                - β ω j * A.mulVec (y ω) i + A.mulVec (y ω) i * A.mulVec (y ω) j) := by
          funext ω; ring
        rw [e]
        exact (((hββ i j).sub (vsm_int_cross μ y β hβy A i j)).sub
          (vsm_int_cross μ y β hβy A j i)).add (vsm_int_quad μ y hyy A A i j)
      have e2 : (fun ω => (β ω i - A.mulVec (y ω) i) * P i j *
            (β ω j - A.mulVec (y ω) j))
          = (fun ω => P i j * ((β ω i - A.mulVec (y ω) i) *
            (β ω j - A.mulVec (y ω) j))) := by
        funext ω; ring
      rw [e2]
      exact h1.const_mul _
    rw [integral_finset_sum _ (fun i _ => by
      apply integrable_finset_sum; intro j _; exact hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : (fun ω => (β ω i - A.mulVec (y ω) i) * P i j *
          (β ω j - A.mulVec (y ω) j))
        = (fun ω => P i j * ((β ω i - A.mulVec (y ω) i) *
          (β ω j - A.mulVec (y ω) j))) := by
      funext ω; ring
    rw [e2, integral_const_mul,
      vsm_err_cov μ y β hyy hβy hββ Syy hSyy Sβy hSβy Sββ hSββ A i j]
    simp only [Matrix.add_apply, Matrix.sub_apply]
  -- the covariance difference is `D Syy Dᵀ`
  have hSyysymm : Syyᵀ = Syy := by
    ext i j
    rw [Matrix.transpose_apply, ← hSyy j i, ← hSyy i j]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hK₀Syy : K₀ * Syy = Sβy := by
    rw [hK₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul Syy hdet, Matrix.mul_one]
  have hSyyK₀T : Syy * K₀ᵀ = Sβyᵀ := by
    have h : (K₀ * Syy)ᵀ = Sβyᵀ := by rw [hK₀Syy]
    rw [Matrix.transpose_mul, hSyysymm] at h
    exact h
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin m) ℝ, D = K - K₀ := ⟨_, rfl⟩
  have hKD : K = K₀ + D := by rw [hD]; abel
  have hdiff : (Sββ - Sβy * Kᵀ - K * Sβyᵀ + K * Syy * Kᵀ)
      = (Sββ - Sβy * K₀ᵀ - K₀ * Sβyᵀ + K₀ * Syy * K₀ᵀ) + D * Syy * Dᵀ := by
    rw [hKD, Matrix.transpose_add]
    simp only [Matrix.add_mul, Matrix.mul_add]
    rw [show K₀ * Syy * Dᵀ = Sβy * Dᵀ by rw [hK₀Syy]]
    rw [show D * Syy * K₀ᵀ = D * Sβyᵀ by rw [Matrix.mul_assoc, hSyyK₀T]]
    abel
  -- the `P`-pairing of `D Syy Dᵀ` is nonnegative
  have hnn : 0 ≤ ∑ i, ∑ j, P i j * (D * Syy * Dᵀ) i j := by
    have hpt : ∀ ω, 0 ≤ ∑ i, ∑ j, P i j * (D.mulVec (y ω) i * D.mulVec (y ω) j) := by
      intro ω
      have h := hP.dotProduct_mulVec_nonneg (D.mulVec (y ω))
      have e : (star (D.mulVec (y ω))) ⬝ᵥ (P.mulVec (D.mulVec (y ω)))
          = ∑ i, ∑ j, P i j * (D.mulVec (y ω) i * D.mulVec (y ω) j) := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, Pi.star_apply,
          RCLike.star_def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e] at h
      exact h
    have hint : ∀ i j : Fin n,
        Integrable (fun ω => P i j * (D.mulVec (y ω) i * D.mulVec (y ω) j)) μ :=
      fun i j => (vsm_int_quad μ y hyy D D i j).const_mul _
    have hsum : (∫ ω, (∑ i, ∑ j, P i j * (D.mulVec (y ω) i * D.mulVec (y ω) j)) ∂μ)
        = ∑ i, ∑ j, P i j * (D * Syy * Dᵀ) i j := by
      rw [integral_finset_sum _ (fun i _ => by
        apply integrable_finset_sum; intro j _; exact hint i j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun j _ => hint i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, vsm_quad_int μ y hyy Syy hSyy D D i j]
    rw [← hsum]
    exact integral_nonneg (fun ω => hpt ω)
  rw [hcrit K₀, hcrit K, hdiff]
  have hsplit : ∑ i, ∑ j, P i j *
      (((Sββ - Sβy * K₀ᵀ - K₀ * Sβyᵀ + K₀ * Syy * K₀ᵀ) + D * Syy * Dᵀ) i j)
      = (∑ i, ∑ j, P i j * (Sββ - Sβy * K₀ᵀ - K₀ * Sβyᵀ + K₀ * Syy * K₀ᵀ) i j)
        + ∑ i, ∑ j, P i j * (D * Syy * Dᵀ) i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.add_apply]
    ring
  rw [hsplit]
  linarith [hnn]
