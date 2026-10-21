-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P15.proposition_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:43:51.777783+00:00
-- url     : https://prove2.me/submissions/c5af38c8-4d32-4c90-9514-0488f180af64

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace G59Q
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma tr_nonneg {P Q : Matrix I I ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ (P * Q).trace.re := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hQ
  rw [Matrix.nonneg_iff_posSemidef] at hP
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hP.mul_mul_conjTranspose_same B).trace_nonneg).1

lemma tr_mono_right {X Y Z : Matrix I I ℂ} (hX : 0 ≤ X) (hYZ : Y ≤ Z) :
    (X * Y).trace.re ≤ (X * Z).trace.re := by
  have := tr_nonneg hX (sub_nonneg.2 hYZ)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma tr_mono_left {X X' Y : Matrix I I ℂ} (hXX : X ≤ X') (hY : 0 ≤ Y) :
    (X * Y).trace.re ≤ (X' * Y).trace.re := by
  have := tr_nonneg (sub_nonneg.2 hXX) hY
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma rpow_eq {A : Matrix I I ℂ} (hA : 0 ≤ A) (s : ℝ) :
    QAlgorithms.Papers.Independent.Claimed50.P15.positiveMatrixRpow A s = A ^ s := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P15.positiveMatrixRpow
  rw [CFC.rpow_eq_cfc_real hA]

lemma rpow_mul {A : Matrix I I ℂ} (hA : A.PosDef) (s : ℝ) : A ^ (1 - s) * A ^ s = A := by
  have hu : IsUnit A := hA.isStrictlyPositive.isUnit
  rw [← CFC.rpow_add hu, sub_add_cancel, CFC.rpow_one A hA.posSemidef.nonneg]


lemma parts (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma traceNorm_herm {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma audenaert (A B : Matrix I I ℂ) (hA : A.PosDef) (hB : B.PosDef) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A.trace.re + B.trace.re - QAlgorithms.traceNorm (A - B)) / 2 ≤
      (A ^ (1 - s) * B ^ s).trace.re := by
  have hH : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  set P := cfc (fun t : ℝ => max t 0) (A - B) with hP
  set Nn := cfc (fun t : ℝ => max (-t) 0) (A - B) with hN
  have hP0 : 0 ≤ P := cfc_nonneg (fun t _ => le_max_right _ _)
  have hN0 : 0 ≤ Nn := cfc_nonneg (fun t _ => le_max_right _ _)
  have hpn : P - Nn = A - B := parts _ hH
  rw [traceNorm_herm hH, ← hP, ← hN]
  have htr : A.trace.re - B.trace.re = P.trace.re - Nn.trace.re := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Complex.sub_re, ← Matrix.trace_sub, hpn]
  set C := B + P with hC
  have hCpd : C.PosDef := hB.add_posSemidef (Matrix.nonneg_iff_posSemidef.1 hP0)
  have hA0 : 0 ≤ A := hA.posSemidef.nonneg
  have hB0 : 0 ≤ B := hB.posSemidef.nonneg
  have hAC : A ≤ C := by
    have : A = B + P - Nn := by rw [add_sub_assoc, hpn]; abel
    rw [this, hC]; exact sub_le_self _ hN0
  have hBC : B ≤ C := le_add_of_nonneg_right hP0
  have hs1 : 1 - s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : (A ^ (1 - s) * A ^ s).trace.re ≤ (A ^ (1 - s) * C ^ s).trace.re :=
    tr_mono_right CFC.rpow_nonneg (CFC.rpow_le_rpow hs hAC)
  have h2 : (A ^ (1 - s) * (C ^ s - B ^ s)).trace.re ≤ (C ^ (1 - s) * (C ^ s - B ^ s)).trace.re :=
    tr_mono_left (CFC.rpow_le_rpow hs1 hAC) (sub_nonneg.2 (CFC.rpow_le_rpow hs hBC))
  have h3 : (B ^ (1 - s) * B ^ s).trace.re ≤ (C ^ (1 - s) * B ^ s).trace.re :=
    tr_mono_left (CFC.rpow_le_rpow hs1 hBC) CFC.rpow_nonneg
  rw [rpow_mul hA] at h1
  rw [rpow_mul hB] at h3
  rw [Matrix.mul_sub, Matrix.mul_sub, rpow_mul hCpd, Matrix.trace_sub, Matrix.trace_sub,
    Complex.sub_re, Complex.sub_re] at h2
  have hCt : C.trace.re = B.trace.re + P.trace.re := by
    rw [hC, Matrix.trace_add, Complex.add_re]
  linarith

end G59Q

open QAlgorithms.Papers.Independent.Claimed50.P15

theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A.trace.re + B.trace.re - QAlgorithms.traceNorm (A - B)) / 2 ≤
      (positiveMatrixRpow A (1 - s) * positiveMatrixRpow B s).trace.re := by
  rw [G59Q.rpow_eq hA.posSemidef.nonneg, G59Q.rpow_eq hB.posSemidef.nonneg]
  exact G59Q.audenaert A B hA hB s hs

end
