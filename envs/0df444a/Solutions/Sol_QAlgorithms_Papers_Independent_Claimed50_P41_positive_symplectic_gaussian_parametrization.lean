-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.positive_symplectic_gaussian_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:25:41.738761+00:00
-- url     : https://prove2.me/submissions/9b6cfe94-2056-4645-b903-462c5d65213b

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PosSymp

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

lemma sqrt_mul_self (u : Matrix (Fin n) (Fin n) ℝ) (hu : u.PosDef) :
    positiveSqrt u * positiveSqrt u = u := by
  unfold positiveSqrt
  have hsa : IsSelfAdjoint u := hu.isHermitian
  rw [← cfc_mul (fun x => Real.sqrt x) (fun x => Real.sqrt x) u]
  conv_rhs => rw [← cfc_id' ℝ u]
  apply cfc_congr
  intro x hx
  have : 0 < x := by
    rw [hu.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hu.eigenvalues_pos i
  simp [Real.mul_self_sqrt this.le]

lemma sqrt_transpose (u : Matrix (Fin n) (Fin n) ℝ) :
    (positiveSqrt u).transpose = positiveSqrt u := by
  unfold positiveSqrt
  have : IsSelfAdjoint (cfc Real.sqrt u) := cfc_predicate _ _
  have h2 : (cfc Real.sqrt u).IsHermitian := this
  simpa [Matrix.IsHermitian] using h2

/-- The basic facts about `s = √u` and `si = s⁻¹` used below. -/
structure SqrtData (u s si : Matrix (Fin n) (Fin n) ℝ) : Prop where
  sq : s * s = u
  st : s.transpose = s
  sit : si.transpose = si
  ssi : s * si = 1
  sis : si * s = 1

lemma sqrtData (u : Matrix (Fin n) (Fin n) ℝ) (hu : u.PosDef) :
    SqrtData u (positiveSqrt u) (positiveSqrt u)⁻¹ := by
  have hsq := sqrt_mul_self u hu
  have hdet : IsUnit (positiveSqrt u).det := by
    have h1 : IsUnit u.det := hu.isUnit.map Matrix.detMonoidHom
    rw [← hsq, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  refine ⟨hsq, sqrt_transpose u, ?_, Matrix.mul_nonsing_inv _ hdet,
    Matrix.nonsing_inv_mul _ hdet⟩
  rw [Matrix.transpose_nonsing_inv, sqrt_transpose]

lemma SqrtData.ssiX {u s si : Matrix (Fin n) (Fin n) ℝ} (h : SqrtData u s si)
    (X : Matrix (Fin n) (Fin n) ℝ) : s * (si * X) = X := by
  rw [← Matrix.mul_assoc, h.ssi, Matrix.one_mul]

lemma SqrtData.sisX {u s si : Matrix (Fin n) (Fin n) ℝ} (h : SqrtData u s si)
    (X : Matrix (Fin n) (Fin n) ℝ) : si * (s * X) = X := by
  rw [← Matrix.mul_assoc, h.sis, Matrix.one_mul]

lemma G_transpose (v s si : Matrix (Fin n) (Fin n) ℝ) (hv : v.IsSymm)
    {u : Matrix (Fin n) (Fin n) ℝ} (h : SqrtData u s si) :
    (Matrix.fromBlocks si 0 (-v * si) s).transpose = Matrix.fromBlocks si (-(si * v)) 0 s := by
  rw [Matrix.fromBlocks_transpose]
  congr 1
  · exact h.sit
  · rw [Matrix.neg_mul, Matrix.transpose_neg, Matrix.transpose_mul, h.sit, hv.eq]
  · exact h.st

lemma back (u v s si : Matrix (Fin n) (Fin n) ℝ) (hv : v.IsSymm) (h : SqrtData u s si) :
    IsPositiveSymplectic (Matrix.fromBlocks si 0 (-v * si) s *
      (Matrix.fromBlocks si 0 (-v * si) s).transpose) := by
  have hGt := G_transpose v s si hv h
  rw [hGt]
  have h1 : Matrix.fromBlocks si 0 (-v * si) s * sigma n * Matrix.fromBlocks si (-(si * v)) 0 s
      = sigma n := by
    unfold sigma
    simp only [Matrix.fromBlocks_multiply]
    simp [h.ssi, h.sis, Matrix.mul_assoc, h.ssiX, h.sisX]
  have h2 : Matrix.fromBlocks si (-(si * v)) 0 s * sigma n * Matrix.fromBlocks si 0 (-v * si) s
      = sigma n := by
    unfold sigma
    simp only [Matrix.fromBlocks_multiply]
    simp [h.ssi, h.sis, Matrix.mul_assoc, h.ssiX, h.sisX]
  constructor
  · unfold PreservesCanonicalForm
    rw [Matrix.transpose_mul, ← hGt, Matrix.transpose_transpose, hGt]
    calc _ = Matrix.fromBlocks si 0 (-v * si) s *
          (Matrix.fromBlocks si (-(si * v)) 0 s * sigma n * Matrix.fromBlocks si 0 (-v * si) s) *
          Matrix.fromBlocks si (-(si * v)) 0 s := by simp only [Matrix.mul_assoc]
      _ = sigma n := by rw [h2, h1]
  · have hinv : Matrix.fromBlocks si 0 (-v * si) s * Matrix.fromBlocks s 0 (si * v) si = 1 := by
      simp only [Matrix.fromBlocks_multiply]
      simp [h.ssi, h.sis, Matrix.mul_assoc, h.ssiX, ← Matrix.fromBlocks_one]
    have := Matrix.PosDef.mul_conjTranspose_self (Matrix.fromBlocks si 0 (-v * si) s) ?_
    · rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hGt] at this
    · intro x y hxy
      have := congrArg (fun z => z ᵥ* Matrix.fromBlocks s 0 (si * v) si) hxy
      simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one] using this

end X4PosSymp

open X4PosSymp QAlgorithms.Papers.Independent.Claimed50.P41 Matrix in
theorem solution (n : ℕ) (hn : 0 < n)
    (P : Matrix (Phase n) (Phase n) ℝ) :
    IsPositiveSymplectic P ↔
      ∃ u v : Matrix (Fin n) (Fin n) ℝ, u.PosDef ∧ v.IsSymm ∧
        P = gaussianSymplectic u v * (gaussianSymplectic u v).transpose := by
  constructor
  · rintro ⟨hS, hP⟩
    set A := P.toBlocks₁₁
    set B := P.toBlocks₁₂
    set C := P.toBlocks₂₁
    set D := P.toBlocks₂₂
    have hPb : P = Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks P).symm
    have hPt : P.transpose = P := by
      have := hP.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [hPb, Matrix.fromBlocks_transpose, Matrix.fromBlocks_inj] at hPt
    obtain ⟨hAt, hCt, hBt, hDt⟩ := hPt
    have hA : A.PosDef := hP.submatrix Sum.inl_injective
    have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
    have hS' := hS
    unfold PreservesCanonicalForm sigma at hS'
    rw [hPb, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hS'
    obtain ⟨e11, e12, -, -⟩ := hS'
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
      Matrix.neg_mul, hAt, hCt, hBt, hDt] at e11 e12
    -- e11 : -(B * A) + A * C = 0, e12 : -(B * B) + A * D = 1
    set Ai := A⁻¹
    have hAiA : Ai * A = 1 := Matrix.nonsing_inv_mul A hAu
    have hAAi : A * Ai = 1 := Matrix.mul_nonsing_inv A hAu
    have hAit : Ai.transpose = Ai := by rw [Matrix.transpose_nonsing_inv, hAt]
    have hAC : A * C = B * A := by
      have := congrArg (· + B * A) e11
      simpa using this
    have hCAi : C * Ai = Ai * B := by
      calc C * Ai = Ai * (A * C) * Ai := by
            rw [← Matrix.mul_assoc, hAiA, Matrix.one_mul]
        _ = Ai * B := by rw [hAC, Matrix.mul_assoc, Matrix.mul_assoc, hAAi, Matrix.mul_one]
    have hAD : A * D = 1 + B * B := by
      have := congrArg (· + B * B) e12
      simp only [neg_add_cancel_comm] at this
      rw [this, add_comm]
    have hD : D = Ai + Ai * (B * B) := by
      calc D = Ai * (A * D) := by rw [← Matrix.mul_assoc, hAiA, Matrix.one_mul]
        _ = _ := by rw [hAD, Matrix.mul_add, Matrix.mul_one]
    have hv : (-(Ai * B)).IsSymm := by
      unfold Matrix.IsSymm
      rw [Matrix.transpose_neg, Matrix.transpose_mul, hAit, hBt, hCAi]
    refine ⟨Ai, -(Ai * B), hA.inv, hv, ?_⟩
    have h := sqrtData Ai hA.inv
    unfold gaussianSymplectic
    rw [G_transpose _ _ _ hv h, Matrix.fromBlocks_multiply, hPb]
    set s := positiveSqrt Ai
    set si := s⁻¹
    have hsisi : si * si = A := by
      calc si * si = si * si * (Ai * A) := by rw [hAiA, Matrix.mul_one]
        _ = si * (si * (s * s)) * A := by rw [h.sq]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h.sisX, h.sis, Matrix.one_mul]
    congr 1
    · rw [hsisi, Matrix.mul_zero, add_zero]
    · rw [Matrix.zero_mul, add_zero, Matrix.mul_neg, Matrix.mul_neg, Matrix.mul_neg, neg_neg,
        ← Matrix.mul_assoc,
        hsisi, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [Matrix.mul_zero, add_zero, Matrix.mul_assoc, hsisi, Matrix.neg_mul, Matrix.neg_mul, neg_neg,
        ← hCAi, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · rw [h.sq, hD]
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      rw [Matrix.mul_assoc (Ai * B) si, ← Matrix.mul_assoc si si, hsisi,
        ← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, Matrix.mul_assoc]
      abel
  · rintro ⟨u, v, hu, hv, rfl⟩
    exact back u v _ _ hv (sqrtData u hu)
