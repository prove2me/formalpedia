-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.fourier_two_di_affine_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:51:34.084035+00:00
-- url     : https://prove2.me/submissions/1fa4ddee-8fa8-42f2-8e60-9e53cecfcac8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- `1/√2` as a complex number. -/
private def x8s : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

private lemma x8s_mul : x8s * x8s = 1 / 2 := by
  rw [x8s, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

@[simp] private lemma x8s_star : star x8s = x8s := Complex.conj_ofReal _

@[simp] private lemma x8s_conj : (starRingEnd ℂ) x8s = x8s := Complex.conj_ofReal _

private lemma x8_qft2 : qftMatrix 2 = !![x8s, x8s; x8s, -x8s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qftMatrix, x8s, div_eq_mul_inv]
  have : (2 * (Real.pi : ℂ) * Complex.I * 2⁻¹) = Real.pi * Complex.I := by ring
  rw [this, Complex.exp_pi_mul_I]; ring

private lemma x8_fourier2 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    fourierChannel 2 X = !![x8s, x8s; x8s, -x8s] * X * (!![x8s, x8s; x8s, -x8s])ᴴ := by
  rw [fourierChannel, conjSuperop, x8_qft2]

private lemma x8_channel_trace {M : Superop (Fin 2) (Fin 2)} (h : IsChannel M)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : (M X).trace = X.trace := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X ((E _)ᴴ)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

private lemma x8_channel_zero {M : Superop (Fin 2) (Fin 2)} (h : IsChannel M) : M 0 = 0 := by
  obtain ⟨m, E, hK, hM⟩ := h
  rw [hM, krausApply]; simp

private lemma x8_lower (t : ℝ) (M : Superop (Fin 2) (Fin 2)) (hM : Free .di M)
    (hP : ((t : ℂ) • choi M - choi (fourierChannel 2)).PosSemidef) : 2 ≤ t := by
  have hz : ∀ (a a' b : Fin 2), a ≠ a' → M (Matrix.single a a' 1) b b = 0 := by
    intro a a' b hne
    have h := congrFun (congrFun (hM.2 (Matrix.single a a' 1)) b) b
    have hd : dephasing (Matrix.single a a' (1 : ℂ)) = 0 := by
      ext i j
      by_cases h : i = j
      · subst h; by_cases h' : a = i <;> simp [dephasing, Matrix.single_apply, h', Ne.symm hne, hne]
        rintro rfl; exact hne h'
      · simp [dephasing, Matrix.diagonal_apply, h]
    rw [hd, x8_channel_zero hM.1] at h
    simpa [dephasing, Matrix.diagonal_apply] using h
  have htr : ∀ a : Fin 2, M (Matrix.single a a 1) 0 0 + M (Matrix.single a a 1) 1 1 = 1 := by
    intro a
    have := x8_channel_trace hM.1 (Matrix.single a a 1)
    simpa [Matrix.trace, Fin.sum_univ_two] using this
  have h0 := hP.dotProduct_mulVec_nonneg (fun p => if p.2 = 0 then 1 else 0)
  have h1 := hP.dotProduct_mulVec_nonneg
    (fun p => if p.2 = 1 then (if p.1 = 0 then 1 else -1) else 0)
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, choi,
    x8_fourier2, Matrix.mul_apply, hz, Matrix.vecMul, Matrix.single_apply] at h0 h1
  have hsum : (0 : ℂ) ≤ ((2 * t - 4 : ℝ) : ℂ) := by
    have := add_nonneg (sub_nonneg.2 h0) h1
    convert this using 1
    push_cast
    linear_combination (-(t : ℂ)) * htr 0 + (-(t : ℂ)) * htr 1 + 8 * x8s_mul
  have := Complex.zero_le_real.mp hsum
  linarith

private def x8K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![!![x8s, 0; x8s, 0], !![0, x8s; 0, -x8s]]

private lemma x8K_kraus : IsKrausFamily x8K := by
  unfold IsKrausFamily
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x8K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    linear_combination 2 * x8s_mul

private lemma x8K_dephase (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply x8K (dephasing X) = krausApply x8K X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [krausApply, x8K, dephasing, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, Matrix.diagonal_apply]

private lemma x8K_free : Free .di (krausApply x8K) :=
  ⟨⟨2, x8K, x8K_kraus, fun _ => rfl⟩, fun X => by rw [x8K_dephase]⟩

private lemma x8K_psd :
    (((2 : ℝ) : ℂ) • choi (krausApply x8K) - choi (fourierChannel 2)).PosSemidef := by
  have e : ((2 : ℝ) : ℂ) • choi (krausApply x8K) - choi (fourierChannel 2) =
      Matrix.vecMulVec (fun p : Fin 2 × Fin 2 =>
        !![x8s, x8s; x8s, -x8s] p.2 p.1 * (if p.1 = 0 then 1 else -1))
        (star (fun p : Fin 2 × Fin 2 =>
        !![x8s, x8s; x8s, -x8s] p.2 p.1 * (if p.1 = 0 then 1 else -1))) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
      simp [choi, krausApply, x8K, x8_fourier2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.vecMulVec_apply, Matrix.single_apply, Matrix.vecMul, dotProduct] <;> ring_nf
  rw [e]; exact Matrix.posSemidef_vecMulVec_self_star _

private lemma x8_maxRob : maxRobustness .di (fourierChannel 2) = 2 := by
  unfold maxRobustness
  apply le_antisymm
  · apply sInf_le
    exact ⟨2, by norm_num, by simp, krausApply x8K, x8K_free, x8K_psd⟩
  · apply le_sInf
    rintro s ⟨t, -, rfl, M, hM, hP⟩
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (x8_lower t M hM hP)

/-- Measure-and-prepare Kraus operators `|v i⟩⟨i|`. -/
private def x8mpK (v : Fin 2 → Fin 2 → ℂ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => Matrix.of fun b a => if a = i then v i b else 0

private lemma x8mp_free (v : Fin 2 → Fin 2 → ℂ)
    (hv : ∀ i, conj (v i 0) * v i 0 + conj (v i 1) * v i 1 = 1) :
    Free .di (krausApply (x8mpK v)) := by
  refine ⟨⟨2, x8mpK v, ?_, fun _ => rfl⟩, fun X => ?_⟩
  · unfold IsKrausFamily
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x8mpK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hv]
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [krausApply, x8mpK, dephasing, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply]

/-- The overlap coefficients. -/
private def x8c (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (i b : Fin 2) : ℂ :=
  ∑ r : Fin 2, conj (x8s * ψ (r, 0) + (if b = 0 then x8s else -x8s) * ψ (r, 1)) * ψ (r, i)

private def x8phi (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (p : Fin 2 × Fin 2) : ℂ :=
  x8s * ψ (p.1, 0) + (if p.2 = 0 then x8s else -x8s) * ψ (p.1, 1)

private lemma x8_F_entry (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (p q : Fin 2 × Fin 2) :
    idTensorSuperop (R := Fin 2) (fourierChannel 2) (pureDensity ψ) p q =
      x8phi ψ p * conj (x8phi ψ q) := by
  obtain ⟨r, b⟩ := p
  obtain ⟨r', b'⟩ := q
  fin_cases b <;> fin_cases b' <;>
    simp [idTensorSuperop, x8_fourier2, pureDensity, x8phi, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma x8_M_entry (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (v : Fin 2 → Fin 2 → ℂ)
    (p q : Fin 2 × Fin 2) :
    idTensorSuperop (R := Fin 2) (krausApply (x8mpK v)) (pureDensity ψ) p q =
      ∑ i : Fin 2, v i p.2 * ψ (p.1, i) * conj (ψ (q.1, i)) * conj (v i q.2) := by
  obtain ⟨r, b⟩ := p
  obtain ⟨r', b'⟩ := q
  simp [idTensorSuperop, pureDensity, krausApply, x8mpK, Matrix.mul_apply,
      Fin.sum_univ_two]
  ring

private lemma x8_val (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (v : Fin 2 → Fin 2 → ℂ) :
    ((idTensorSuperop (R := Fin 2) (fourierChannel 2) (pureDensity ψ)) *
      (idTensorSuperop (R := Fin 2) (krausApply (x8mpK v)) (pureDensity ψ))).trace =
    ∑ i : Fin 2, (v i 0 * x8c ψ i 0 + v i 1 * x8c ψ i 1) *
      conj (v i 0 * x8c ψ i 0 + v i 1 * x8c ψ i 1) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, x8_F_entry, x8_M_entry]
  simp [x8c, x8phi, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private lemma x8_alg (a b : ℂ) (h1 : Complex.normSq a = Complex.normSq b)
    (h2 : Complex.normSq (3 / 5 * a + 4 / 5 * b) = Complex.normSq a)
    (h3 : Complex.normSq (3 / 5 * a + 4 / 5 * Complex.I * b) = Complex.normSq a) :
    a = 0 ∧ b = 0 := by
  rw [Complex.normSq_apply, Complex.normSq_apply] at h1
  rw [Complex.normSq_apply, Complex.normSq_apply] at h2 h3
  simp at h2 h3
  have e1 : a.re * b.re + a.im * b.im = 0 := by nlinarith
  have e2 : a.im * b.re - a.re * b.im = 0 := by nlinarith
  have e3 : (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2) = 0 := by nlinarith
  have ha : a.re ^ 2 + a.im ^ 2 = 0 := by
    rcases mul_eq_zero.1 e3 with h | h
    · exact h
    · nlinarith
  have hb : b.re ^ 2 + b.im ^ 2 = 0 := by nlinarith
  refine ⟨Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩ <;> simp <;> nlinarith

private lemma x8_rel (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    x8c ψ 0 0 + x8c ψ 0 1 + x8c ψ 1 0 - x8c ψ 1 1 =
      2 * x8s * ∑ p, conj (ψ p) * ψ p := by
  simp [x8c, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private lemma x8_norm (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hψ : ‖ψ‖ = 1) :
    ∑ p, conj (ψ p) * ψ p = 1 := by
  have h := EuclideanSpace.norm_sq_eq ψ
  rw [hψ] at h
  have e : ∑ p, conj (ψ p) * ψ p = ((∑ p, ‖ψ p‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [e, ← h]; simp

theorem x8_main : maxRobustness .di (fourierChannel 2) = 2 ∧
    isometricAffineMinRobustness .di (fourierChannel 2) = 0 := by
  refine ⟨x8_maxRob, ?_⟩
  unfold isometricAffineMinRobustness
  rw [ENNReal.inv_eq_zero, sInf_eq_top]
  rintro s ⟨t, -, -, ψ, hψ, hM⟩
  exfalso
  have key : ∀ v : Fin 2 → Fin 2 → ℂ,
      (∀ i, conj (v i 0) * v i 0 + conj (v i 1) * v i 1 = 1) →
      Complex.normSq (v 0 0 * x8c ψ 0 0 + v 0 1 * x8c ψ 0 1) +
        Complex.normSq (v 1 0 * x8c ψ 1 0 + v 1 1 * x8c ψ 1 1) = t := by
    intro v hv
    have := hM _ (x8mp_free v hv)
    rw [x8_val] at this
    simpa only [Fin.sum_univ_two, Complex.mul_conj, Complex.add_re, Complex.ofReal_re] using this
  have pair : ∀ u w : Fin 2 → ℂ, conj (u 0) * u 0 + conj (u 1) * u 1 = 1 →
      conj (w 0) * w 0 + conj (w 1) * w 1 = 1 →
      Complex.normSq (u 0 * x8c ψ 0 0 + u 1 * x8c ψ 0 1) +
        Complex.normSq (w 0 * x8c ψ 1 0 + w 1 * x8c ψ 1 1) = t :=
    fun u w hu hw => key ![u, w] (by intro i; fin_cases i <;> simpa)
  have ue0 : conj ((![1, 0] : Fin 2 → ℂ) 0) * (![1, 0] : Fin 2 → ℂ) 0 +
      conj ((![1, 0] : Fin 2 → ℂ) 1) * (![1, 0] : Fin 2 → ℂ) 1 = 1 := by simp
  have ue1 : conj ((![0, 1] : Fin 2 → ℂ) 0) * (![0, 1] : Fin 2 → ℂ) 0 +
      conj ((![0, 1] : Fin 2 → ℂ) 1) * (![0, 1] : Fin 2 → ℂ) 1 = 1 := by simp
  have uf : conj ((![3 / 5, 4 / 5] : Fin 2 → ℂ) 0) * (![3 / 5, 4 / 5] : Fin 2 → ℂ) 0 +
      conj ((![3 / 5, 4 / 5] : Fin 2 → ℂ) 1) * (![3 / 5, 4 / 5] : Fin 2 → ℂ) 1 = 1 := by
    simp [map_div₀, map_ofNat]; norm_num
  have ug : conj ((![3 / 5, 4 / 5 * Complex.I] : Fin 2 → ℂ) 0) *
      (![3 / 5, 4 / 5 * Complex.I] : Fin 2 → ℂ) 0 +
      conj ((![3 / 5, 4 / 5 * Complex.I] : Fin 2 → ℂ) 1) *
      (![3 / 5, 4 / 5 * Complex.I] : Fin 2 → ℂ) 1 = 1 := by
    simp [map_div₀, map_ofNat]; ring_nf; rw [Complex.I_sq]; norm_num
  have k00 := pair _ _ ue0 ue0
  have k10 := pair _ _ ue1 ue0
  have kf0 := pair _ _ uf ue0
  have kg0 := pair _ _ ug ue0
  have k01 := pair _ _ ue0 ue1
  have k0f := pair _ _ ue0 uf
  have k0g := pair _ _ ue0 ug
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero, zero_add]
    at k00 k10 kf0 kg0 k01 k0f k0g
  obtain ⟨h00, h01⟩ := x8_alg (x8c ψ 0 0) (x8c ψ 0 1) (by linarith) (by linarith) (by linarith)
  obtain ⟨h10, h11⟩ := x8_alg (x8c ψ 1 0) (x8c ψ 1 1) (by linarith) (by linarith) (by linarith)
  have hr := x8_rel ψ
  rw [h00, h01, h10, h11, x8_norm ψ hψ] at hr
  have : x8s = 0 := by linear_combination -hr / 2
  have := x8s_mul
  simp_all

end QAlgorithms.Papers.Independent.Information100.P34

open QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution :
    maxRobustness .di (fourierChannel 2) = 2 ∧
    isometricAffineMinRobustness .di (fourierChannel 2) = 0 := x8_main
