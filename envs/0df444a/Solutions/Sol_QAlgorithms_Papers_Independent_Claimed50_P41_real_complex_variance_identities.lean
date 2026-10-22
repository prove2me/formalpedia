-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.real_complex_variance_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:45:03.381928+00:00
-- url     : https://prove2.me/submissions/83ec17c6-9d4f-4c4a-8251-6c533b2832ed

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_cc : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma g68k_cf {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) (i j : Fin n) :
    complexForm V (Sum.inl i) (Sum.inl j) = (1 / 2 : ℂ) * ((V (Sum.inl i) (Sum.inl j) : ℂ) +
      V (Sum.inr i) (Sum.inr j) + Complex.I * (V (Sum.inr i) (Sum.inl j) - V (Sum.inl i) (Sum.inr j))) ∧
    complexForm V (Sum.inl i) (Sum.inr j) = (1 / 2 : ℂ) * ((V (Sum.inl i) (Sum.inl j) : ℂ) -
      V (Sum.inr i) (Sum.inr j) + Complex.I * (V (Sum.inr i) (Sum.inl j) + V (Sum.inl i) (Sum.inr j))) ∧
    complexForm V (Sum.inr i) (Sum.inl j) = (1 / 2 : ℂ) * ((V (Sum.inl i) (Sum.inl j) : ℂ) -
      V (Sum.inr i) (Sum.inr j) - Complex.I * (V (Sum.inr i) (Sum.inl j) + V (Sum.inl i) (Sum.inr j))) ∧
    complexForm V (Sum.inr i) (Sum.inr j) = (1 / 2 : ℂ) * ((V (Sum.inl i) (Sum.inl j) : ℂ) +
      V (Sum.inr i) (Sum.inr j) - Complex.I * (V (Sum.inr i) (Sum.inl j) - V (Sum.inl i) (Sum.inr j))) := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [complexForm, canonicalCoordinateMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply, complexify, smul_eq_mul]
    simp only [Complex.star_def, apply_ite (starRingEnd ℂ), map_zero, map_mul, map_inv₀,
      Complex.conj_ofReal, Complex.conj_I, map_neg, map_one]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_add_distrib]
    have h2' : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by rw [sq, h2]
    ring_nf
    simp only [h2', Complex.I_sq]
    ring

lemma g68k_omega_unit (n : ℕ) :
    canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h2' : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by rw [sq, h2]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
  · simp only [canonicalCoordinateMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply, smul_eq_mul, Matrix.neg_apply]
    simp only [Complex.star_def, apply_ite (starRingEnd ℂ), map_zero, map_mul, map_inv₀,
      Complex.conj_ofReal, Complex.conj_I, map_neg, map_one]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false]
    split_ifs <;> ring_nf <;> simp only [h2', Complex.I_sq] <;> ring

lemma g68k_complexify_posDef {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.PosDef) :
    (complexify V).PosDef := by
  have hs : ∀ i j, V j i = V i j := fun i j => by
    have := hV.1.apply i j; simpa using this
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j; simp [complexify, Matrix.conjTranspose_apply, hs]
  · set a : Phase n → ℝ := fun i => (x i).re
    set b : Phase n → ℝ := fun i => (x i).im
    have key : dotProduct (star x) ((complexify V).mulVec x) =
        ((dotProduct a (V.mulVec a) + dotProduct b (V.mulVec b) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.re_sum,
          Complex.ofReal_re, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp [Complex.mul_re, Complex.mul_im, a, b]
      · simp only [dotProduct, Matrix.mulVec, complexify, Pi.star_apply, Complex.im_sum,
          Complex.ofReal_im, Finset.mul_sum]
        have : ∀ i j, (star (x i) * ((V i j : ℂ) * x j)).im =
            V i j * (a i * b j) - V i j * (b i * a j) := by
          intro i j; simp [Complex.mul_re, Complex.mul_im, a, b]; ring
        simp only [this, Finset.sum_sub_distrib]
        rw [sub_eq_zero, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hs]; ring
    rw [key, Complex.zero_lt_real]
    have hpa := (hV.posSemidef).dotProduct_mulVec_nonneg a
    have hpb := (hV.posSemidef).dotProduct_mulVec_nonneg b
    simp only [star_trivial] at hpa hpb
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb; apply hx; funext i
        apply Complex.ext
        · exact congrFun ha i
        · exact congrFun hb i
      have := hV.dotProduct_mulVec_pos hb
      simp only [star_trivial] at this
      linarith
    · have := hV.dotProduct_mulVec_pos ha
      simp only [star_trivial] at this
      linarith



/-- PDF p.29, (8.5)–(8.6): the complete real/complex matrix identities.
The operator-moment construction is handled separately; these identities apply
to every real symmetric matrix, as the source's formulas themselves do. -/
theorem solution (n : ℕ) (hn : 0 < n)
    (Vone Vtwo Vthree : Matrix (Fin n) (Fin n) ℝ)
    (hVone : Vone.IsSymm) (hVthree : Vthree.IsSymm) :
    let V := Matrix.fromBlocks Vone Vtwo Vtwo.transpose Vthree
    let A := noiseA V
    let B := noiseB V
    A.IsHermitian ∧ B.IsSymm ∧
    complexForm V = Matrix.fromBlocks A B (fun i j => star (B i j)) (fun i j => star (A i j)) ∧
    A = (1 / 2 : ℂ) • (complexify Vone + complexify Vthree +
      Complex.I • (complexify Vtwo.transpose - complexify Vtwo)) ∧
    B = (1 / 2 : ℂ) • (complexify Vone - complexify Vthree +
      Complex.I • (complexify Vtwo.transpose + complexify Vtwo)) ∧
    complexify Vone = (1 / 2 : ℂ) •
      (A + A.map star + B + B.map star) ∧
    complexify Vtwo = (Complex.I / 2) •
      (A - A.map star - B + B.map star) ∧
    complexify Vthree = (1 / 2 : ℂ) •
      (A + A.map star - B - B.map star) ∧
    (V.PosDef → (complexForm V).PosDef) := by
  intro V A B
  have s1 : ∀ i j, Vone j i = Vone i j := fun i j => by
    simpa using congrFun (congrFun hVone i) j
  have s3 : ∀ i j, Vthree j i = Vthree i j := fun i j => by
    simpa using congrFun (congrFun hVthree i) j
  have hA : ∀ i j, A i j = (1 / 2 : ℂ) * ((Vone i j : ℂ) + Vthree i j +
      Complex.I * (Vtwo j i - Vtwo i j)) := by
    intro i j
    simp only [A, noiseA, Matrix.submatrix_apply, (g68k_cf V i j).1]
    simp [V]
  have hB : ∀ i j, B i j = (1 / 2 : ℂ) * ((Vone i j : ℂ) - Vthree i j +
      Complex.I * (Vtwo j i + Vtwo i j)) := by
    intro i j
    simp only [B, noiseB, Matrix.submatrix_apply, (g68k_cf V i j).2.1]
    simp [V]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, hA, hA, s1, s3]
    apply Complex.ext <;> simp <;> ring
  · ext i j
    rw [Matrix.transpose_apply, hB, hB, s1, s3]
    ring
  · ext a b
    rcases a with i | i <;> rcases b with j | j
    · show complexForm V (Sum.inl i) (Sum.inl j) = A i j; rfl
    · show complexForm V (Sum.inl i) (Sum.inr j) = B i j; rfl
    · show complexForm V (Sum.inr i) (Sum.inl j) = star (B i j)
      rw [(g68k_cf V i j).2.2.1, hB]
      apply Complex.ext <;> simp [V] <;> ring
    · show complexForm V (Sum.inr i) (Sum.inr j) = star (A i j)
      rw [(g68k_cf V i j).2.2.2, hA]
      apply Complex.ext <;> simp [V] <;> ring
  · ext i j
    rw [hA]; simp [complexify]
  · ext i j
    rw [hB]; simp [complexify]; ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply, hA, hB, complexify]
    apply Complex.ext <;> simp <;> ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, hA, hB,
      complexify]
    apply Complex.ext <;> simp <;> ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, hA, hB,
      complexify]
    apply Complex.ext <;> simp <;> ring
  · intro hV
    have hinj : Function.Injective (canonicalCoordinateMatrix n).vecMul := by
      intro x y hxy
      have := congrArg (fun z => Matrix.vecMul z (canonicalCoordinateMatrix n).conjTranspose) hxy
      simpa [Matrix.vecMul_vecMul, g68k_omega_unit] using this
    exact (g68k_complexify_posDef V hV).mul_mul_conjTranspose_same hinj



end
