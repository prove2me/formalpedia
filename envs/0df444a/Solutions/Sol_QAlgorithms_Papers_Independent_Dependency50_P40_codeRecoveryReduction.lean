-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.codeRecoveryReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:19:47.678519+00:00
-- url     : https://prove2.me/submissions/dafb1d80-9ba6-4912-95ce-935c592fb26f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open scoped ComplexStarModule

noncomputable def g53d_saEquiv (n : Type*) [Fintype n] :
    Matrix n n ℂ ≃ₗ[ℝ] (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) where
  toFun M := (ℜ M, ℑ M)
  map_add' x y := by simp
  map_smul' r x := by simp
  invFun p := (p.1 : Matrix n n ℂ) + Complex.I • (p.2 : Matrix n n ℂ)
  left_inv M := realPart_add_I_smul_imaginaryPart M
  right_inv p := by
    ext1
    · simp [realPart_I_smul, selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe]
    · simp [imaginaryPart_I_smul, selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe]

lemma g53d_finrank_sa (n : Type*) [Fintype n] :
    Module.finrank ℝ (selfAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 := by
  haveI : Module.Finite ℝ (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :=
    Module.Finite.equiv (g53d_saEquiv n)
  haveI : Module.Finite ℝ (selfAdjoint (Matrix n n ℂ)) :=
    Module.Finite.of_surjective (LinearMap.fst ℝ _ (selfAdjoint (Matrix n n ℂ)))
      (fun x => ⟨(x, 0), rfl⟩)
  have h := (g53d_saEquiv n).finrank_eq
  rw [Module.finrank_prod] at h
  have h2 : Module.finrank ℝ (Matrix n n ℂ) = Fintype.card n * Fintype.card n * 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]
  rw [h2] at h
  rw [sq]
  omega

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

lemma g53d_enc_apply {a h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (r : Fin a) (i : Fin k) :
    encodedPurification U psi (r, i) = ∑ j, U i j * psi (r, j) := by
  simp [encodedPurification, matrixAction, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul]

def g53d_Phi {a m : ℕ} (φ : EuclideanSpace ℂ (Fin a × Fin m)) : Matrix (Fin m) (Fin a) ℂ :=
  Matrix.of fun j r => φ (r, j)

lemma g53d_tl {a m : ℕ} (φ : EuclideanSpace ℂ (Fin a × Fin m)) :
    traceLeft (pureDensity φ) = g53d_Phi φ * (g53d_Phi φ)ᴴ := by
  ext j l
  simp [traceLeft, pureDensity, Matrix.mul_apply, g53d_Phi]

lemma g53d_norm_sq {a m : ℕ} (φ : EuclideanSpace ℂ (Fin a × Fin m)) :
    ‖φ‖ ^ 2 = ((g53d_Phi φ * (g53d_Phi φ)ᴴ).trace).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, g53d_Phi, Matrix.of_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_re]

lemma g53d_Phi_enc {a h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) :
    g53d_Phi (encodedPurification U psi) = U * g53d_Phi psi := by
  ext i r
  simp [g53d_Phi, g53d_enc_apply, Matrix.mul_apply]

lemma g53d_qf {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) (x y : Fin h → ℂ)
    (Y : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ i', conj ((U *ᵥ x) i) * Y i i' * (U *ᵥ y) i') =
      ∑ j, ∑ j', conj (x j) * (Uᴴ * Y * U) j j' * y j' := by
  have gen : ∀ {n : Type} [Fintype n] (M : Matrix n n ℂ) (u w : n → ℂ),
      (∑ i, ∑ i', conj (u i) * M i i' * w i') = star u ⬝ᵥ (M *ᵥ w) := by
    intro n _ M u w
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [gen, gen]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma g53d_fid {a h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (B : Superop (Fin k) (Fin k)) :
    purificationFidelity (encodedPurification U psi) B =
      purificationFidelity psi (conjSuperop Uᴴ ∘ B ∘ conjSuperop U) := by
  unfold purificationFidelity complexQuadraticForm idTensorSuperop
  congr 1
  have hblk : ∀ r r' : Fin a, (Matrix.of fun i i' =>
      pureDensity (encodedPurification U psi) (r, i) (r', i')) =
      U * (Matrix.of fun j j' => pureDensity psi (r, j) (r', j')) * Uᴴ := by
    intro r r'
    ext i i'
    simp only [pureDensity, Matrix.of_apply, g53d_enc_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [Complex.star_def]
    ring
  simp only [Function.comp, conjSuperop, Matrix.of_apply, hblk, Matrix.conjTranspose_conjTranspose]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r' _ => ?_)
  have := g53d_qf U (fun j => psi (r, j)) (fun j => psi (r', j))
    (B (U * (Matrix.of fun j j' => pureDensity psi (r, j) (r', j')) * Uᴴ))
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [g53d_enc_apply]
  exact this

lemma g53d_R_kraus {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (R : Superop (Fin k) (Fin k)) (hR : IsChannel R) (hc : HasCodeOutputs U R) :
    IsChannel (conjSuperop Uᴴ ∘ R) := by
  obtain ⟨m, E, hK, hRE⟩ := hR
  set P := U * Uᴴ with hP
  have hPh : Pᴴ = P := by rw [hP, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPP : P * P = P := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  set Q : Matrix (Fin k) (Fin k) ℂ := 1 - P with hQ
  have hQh : Qᴴ = Q := by rw [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  have hQP : Q * P = 0 := by rw [hQ, Matrix.sub_mul, hPP]; simp
  have hPQ : P * Q = 0 := by rw [hQ, Matrix.mul_sub, hPP]; simp
  have hQpsd : Q.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Q
    rwa [hQh, hQQ] at this
  have h1 := hc 1
  have hQR : Q * R 1 * Q = 0 := by
    rw [← h1]
    have : Q * (codeProjector U * R 1 * codeProjector U) * Q =
        (Q * P) * R 1 * (P * Q) := by
      simp only [codeProjector, ← hP, Matrix.mul_assoc]
    rw [this, hQP]; simp
  let S := ∑ j, (E j)ᴴ * Q * E j
  have hSpsd : S.PosSemidef :=
    Matrix.posSemidef_sum _ (fun j _ => hQpsd.conjTranspose_mul_mul_same (E j))
  have hStr : S.trace = 0 := by
    have e : S.trace = (Q * R 1 * Q).trace := by
      rw [hRE 1]
      simp only [S, krausApply, Matrix.trace_sum, Matrix.mul_one, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.trace_mul_cycle]
      rw [Matrix.trace_mul_comm (Q * _) Q, ← Matrix.mul_assoc, hQQ, Matrix.trace_mul_comm]
    rw [e, hQR, Matrix.trace_zero]
  have hS0 : S = 0 := (hSpsd.trace_eq_zero_iff).mp hStr
  refine ⟨m, fun j => Uᴴ * E j, ?_, ?_⟩
  · unfold IsKrausFamily
    have : ∀ j, (Uᴴ * E j)ᴴ * (Uᴴ * E j) = (E j)ᴴ * E j - (E j)ᴴ * Q * E j := by
      intro j
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP, Matrix.mul_assoc]
      abel
    simp only [this, Finset.sum_sub_distrib]
    unfold IsKrausFamily at hK
    rw [hK]
    change 1 - S = 1
    rw [hS0, sub_zero]
  · intro rho
    simp only [Function.comp, conjSuperop, hRE rho, krausApply, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma g53d_S_kraus {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (S : Superop (Fin k) (Fin h)) (hS : IsChannel S) : IsChannel (conjSuperop U ∘ S) := by
  obtain ⟨m, E, hK, hSE⟩ := hS
  refine ⟨m, fun j => U * E j, ?_, ?_⟩
  · unfold IsKrausFamily at hK ⊢
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    exact hK
  · intro rho
    simp only [Function.comp, conjSuperop, hSE rho, krausApply, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- PDF pp.4–5, Fig.1 and §V: code-output recoveries correspond exactly to logical-output
channels, preserving the purification objective. The count is real ambient Hermitian
dimension before affine constraints. The p.4 prose prints K tensor H for X_R; changed
to H tensor K because (21), (22) and recovery K → H determine that order. -/
theorem solution {h k a : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k)
    (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (rho : Matrix (Fin k) (Fin k) ℂ) (hrho : IsDensityMatrix rho)
    (hsupp : rho = codeProjector U * rho * codeProjector U)
    (psi : EuclideanSpace ℂ (Fin a × Fin h))
    (hpsi : IsPurification (Uᴴ * rho * U) psi)
    (E : Superop (Fin k) (Fin k)) (hE : IsChannel E) :
    IsPurification rho (encodedPurification U psi) ∧
    (∀ R : Superop (Fin k) (Fin k), IsChannel R → HasCodeOutputs U R →
      IsChannel (conjSuperop Uᴴ ∘ R) ∧
      conjSuperop U ∘ (conjSuperop Uᴴ ∘ R) = R) ∧
    (∀ S : Superop (Fin k) (Fin h), IsChannel S →
      IsChannel (conjSuperop U ∘ S) ∧ HasCodeOutputs U (conjSuperop U ∘ S) ∧
      conjSuperop Uᴴ ∘ (conjSuperop U ∘ S) = S) ∧
    (∀ R : Superop (Fin k) (Fin k), IsChannel R → HasCodeOutputs U R →
      purificationFidelity (encodedPurification U psi) (R ∘ E) =
        purificationFidelity psi ((conjSuperop Uᴴ ∘ R) ∘ E ∘ conjSuperop U)) ∧
    Module.finrank ℝ (selfAdjoint (Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ)) = k ^ 4 ∧
    Module.finrank ℝ (selfAdjoint (Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ)) = h ^ 2 * k ^ 2 ∧
    (k : ℝ) ^ 4 / ((h : ℝ) ^ 2 * (k : ℝ) ^ 2) = ((k : ℝ) / (h : ℝ)) ^ 2 := by
  have hPU : codeProjector U * U = U := by
    rw [codeProjector, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hUP : Uᴴ * codeProjector U = Uᴴ := by
    rw [codeProjector, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hU' : ∀ X : Matrix (Fin h) (Fin k) ℂ, Uᴴ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have e := g53d_norm_sq (encodedPurification U psi)
      have e2 := g53d_norm_sq psi
      rw [hpsi.1, one_pow] at e2
      rw [g53d_Phi_enc, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
        Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, ← e2] at e
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp e
    · rw [g53d_tl, g53d_Phi_enc, Matrix.conjTranspose_mul]
      have h2 := hpsi.2
      rw [g53d_tl] at h2
      calc U * g53d_Phi psi * ((g53d_Phi psi)ᴴ * Uᴴ)
          = U * (g53d_Phi psi * (g53d_Phi psi)ᴴ) * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = codeProjector U * rho * codeProjector U := by
            rw [h2, codeProjector]; simp only [Matrix.mul_assoc]
        _ = rho := hsupp.symm
  · intro R hR hc
    refine ⟨g53d_R_kraus U hU R hR hc, ?_⟩
    funext M
    simp only [Function.comp, conjSuperop, Matrix.conjTranspose_conjTranspose]
    rw [← hc M, codeProjector]
    simp only [Matrix.mul_assoc, hU']
  · intro S hS
    refine ⟨g53d_S_kraus U hU S hS, ?_, ?_⟩
    · intro M
      simp only [Function.comp, conjSuperop]
      simp only [codeProjector, Matrix.mul_assoc, hU']
    · funext M
      simp only [Function.comp, conjSuperop, Matrix.conjTranspose_conjTranspose]
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  · intro R hR hc
    exact g53d_fid U psi (R ∘ E)
  · rw [g53d_finrank_sa]; simp [Fintype.card_prod]; ring
  · rw [g53d_finrank_sa]; simp [Fintype.card_prod]; ring
  · have : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp

end
