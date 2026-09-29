-- Prove2me | solution 1 for VectorSpaceOpt.gauss_markov
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T14:09:48.896476+00:00
-- url     : https://prove2.me/submissions/27aa1780-af49-4971-a54b-c497ea4773d2

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

theorem vsm_gm_trace {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = (Wᵀ * Q⁻¹ * W)⁻¹ * Wᵀ * Q⁻¹) :
    K₀ * W = 1 ∧
    (∀ K : Matrix (Fin n) (Fin m) ℝ, K * W = 1 →
      ∀ i, (K₀ * Q * K₀ᵀ) i i ≤ (K * Q * Kᵀ) i i) ∧
    K₀ * Q * K₀ᵀ = (Wᵀ * Q⁻¹ * W)⁻¹ := by
  classical
  have hQu : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hQi : (Q⁻¹).PosDef := Matrix.posDef_inv_iff.2 hQ
  have hinj : ∀ x : Fin n → ℝ, W.mulVec x = 0 → x = 0 := by
    intro x hx
    funext j
    refine (Fintype.linearIndependent_iff.1 hW) x ?_ j
    funext i
    have hi : W.mulVec x i = 0 := congrFun hx i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hi]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hWinj : Function.Injective W.mulVec := by
    intro a b hab
    have h : W.mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    exact sub_eq_zero.1 (hinj _ h)
  set M : Matrix (Fin n) (Fin n) ℝ := Wᵀ * Q⁻¹ * W with hM
  have hMpd : M.PosDef := by
    have h := hQi.conjTranspose_mul_mul_same hWinj
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rwa [hM]
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hMpd.isUnit
  have hQsymm : Qᵀ = Q := by
    have h : Qᴴ = Q := hQ.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hQisymm : (Q⁻¹)ᵀ = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQsymm]
  have hMsymm : Mᵀ = M := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQisymm]
    simp only [Matrix.mul_assoc]
  have hMisymm : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMsymm]
  have hMM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hQQ' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hunb : K₀ * W = 1 := by
    rw [hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Wᵀ * (Q⁻¹ * W) = M by rw [hM]; simp only [Matrix.mul_assoc]]
    exact hMM
  have hK₀T : K₀ᵀ = Q⁻¹ * W * M⁻¹ := by
    rw [hK₀, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hQisymm, hMisymm]
    simp only [Matrix.mul_assoc]
  have hcov : K₀ * Q * K₀ᵀ = M⁻¹ := by
    rw [hK₀T, hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Q⁻¹ * (Q * (Q⁻¹ * (W * M⁻¹))) = Q⁻¹ * (W * M⁻¹) by
      rw [← Matrix.mul_assoc Q⁻¹ Q, hQQ, Matrix.one_mul]]
    rw [show M⁻¹ * (Wᵀ * (Q⁻¹ * (W * M⁻¹))) = M⁻¹ * (M * M⁻¹) by
      rw [hM]; simp only [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc, hMM, Matrix.one_mul]
  refine ⟨hunb, ?_, by rw [hcov, hM]⟩
  intro K hK i
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin n) (Fin m) ℝ, D = K - K₀ := ⟨_, rfl⟩
  have hDW : D * W = 0 := by rw [hDdef, Matrix.sub_mul, hK, hunb, sub_self]
  have hA : K₀ * Q * Dᵀ = 0 := by
    rw [hK₀]
    simp only [Matrix.mul_assoc]
    rw [show Q⁻¹ * (Q * Dᵀ) = Dᵀ by rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]]
    rw [show Wᵀ * Dᵀ = (D * W)ᵀ by rw [Matrix.transpose_mul]]
    rw [hDW, Matrix.transpose_zero, Matrix.mul_zero]
  have hB : D * Q * K₀ᵀ = 0 := by
    rw [hK₀T]
    simp only [Matrix.mul_assoc]
    rw [show Q * (Q⁻¹ * (W * M⁻¹)) = W * M⁻¹ by
      rw [← Matrix.mul_assoc Q Q⁻¹, hQQ', Matrix.one_mul]]
    rw [← Matrix.mul_assoc, hDW, Matrix.zero_mul]
  have hexpand : K * Q * Kᵀ = K₀ * Q * K₀ᵀ + D * Q * Dᵀ := by
    have e : K₀ * Q * K₀ᵀ + D * Q * Dᵀ
        = K * Q * Kᵀ - K₀ * Q * Dᵀ - D * Q * K₀ᵀ := by
      rw [hDdef]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub]
      abel
    rw [e, hA, hB, sub_zero, sub_zero]
  have hpsd : (D * Q * Dᵀ).PosSemidef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same D
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [hexpand]
  simp only [Matrix.add_apply]
  linarith [hpsd.diag_nonneg (i := i)]


theorem solution {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin n) ℝ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (hQ : Q.PosDef)
    (ε : Ω → Fin m → ℝ)
    (hε1 : ∀ i : Fin m, Integrable (fun ω => ε ω i) μ)
    (hε2 : ∀ i j : Fin m, Integrable (fun ω => ε ω i * ε ω j) μ)
    (hmean : ∀ i : Fin m, ∫ ω, ε ω i ∂μ = 0)
    (hcov : ∀ i j : Fin m, ∫ ω, ε ω i * ε ω j ∂μ = Q i j)
    (β : Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (hy : ∀ ω i, y ω i = W.mulVec β i + ε ω i)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = (Wᵀ * Q⁻¹ * W)⁻¹ * Wᵀ * Q⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : K * W = 1) :
    K₀ * W = 1 ∧
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - β i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - β i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (K₀.mulVec (y ω) i - β i) * (K₀.mulVec (y ω) j - β j) ∂μ =
      (Wᵀ * Q⁻¹ * W)⁻¹ i j) := by
  classical
  obtain ⟨h1, h2, h3⟩ := vsm_gm_trace W Q hQ hW K₀ hK₀
  have herr : ∀ (A : Matrix (Fin n) (Fin m) ℝ), A * W = 1 → ∀ (ω : Ω) (i : Fin n),
      A.mulVec (y ω) i - β i = A.mulVec (ε ω) i := by
    intro A hA ω i
    have hsplit : A.mulVec (y ω) i = A.mulVec (W.mulVec β) i + A.mulVec (ε ω) i := by
      have hfun : y ω = (fun k => W.mulVec β k + ε ω k) := funext (fun k => hy ω k)
      rw [hfun]
      simp only [Matrix.mulVec, dotProduct, mul_add]
      exact Finset.sum_add_distrib
    rw [hsplit, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    ring
  refine ⟨h1, ?_, ?_⟩
  · intro i
    have e₀ : (fun ω => (K₀.mulVec (y ω) i - β i) ^ 2)
        = (fun ω => K₀.mulVec (ε ω) i * K₀.mulVec (ε ω) i) := by
      funext ω; rw [herr K₀ h1 ω i]; ring
    have eK : (fun ω => (K.mulVec (y ω) i - β i) ^ 2)
        = (fun ω => K.mulVec (ε ω) i * K.mulVec (ε ω) i) := by
      funext ω; rw [herr K hK ω i]; ring
    rw [e₀, eK, vsm_quad_int μ ε hε2 Q hcov K₀ K₀ i i,
      vsm_quad_int μ ε hε2 Q hcov K K i i]
    exact h2 K hK i
  · intro i j
    have e₀ : (fun ω => (K₀.mulVec (y ω) i - β i) * (K₀.mulVec (y ω) j - β j))
        = (fun ω => K₀.mulVec (ε ω) i * K₀.mulVec (ε ω) j) := by
      funext ω; rw [herr K₀ h1 ω i, herr K₀ h1 ω j]
    rw [e₀, vsm_quad_int μ ε hε2 Q hcov K₀ K₀ i j, h3]
