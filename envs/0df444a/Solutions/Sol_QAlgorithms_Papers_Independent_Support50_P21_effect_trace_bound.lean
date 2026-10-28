-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.effect_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:18:47.350174+00:00
-- url     : https://prove2.me/submissions/663fa700-0a2a-4af1-b7fe-4f0bb5334aaa

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21


noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder

namespace X6D21

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P07

variable {J : Type} [Fintype J] [DecidableEq J]

lemma cfc_spec {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  have hs := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma trace_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma sq_eq_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X * X = cfc (fun x : ℝ => x ^ 2) X := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX]
  conv_lhs => rw [spec hX]
  set U := (hX.eigenvectorUnitary : Matrix J J ℂ)
  calc U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2; funext i; push_cast; ring

lemma traceNorm_herm {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    traceNorm X = ∑ i, |hX.eigenvalues i| := by
  rw [traceNorm, hX.eq, sq_eq_cfc hX, ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) X]
  have : (Real.sqrt ∘ fun x : ℝ => x ^ 2) = fun x => |x| := by
    funext x; simp [Real.sqrt_sq_eq_abs]
  rw [this, trace_cfc hX, Complex.re_sum]
  simp

lemma effect_conj {P : Matrix J J ℂ} (hP : IsEffect P) (U : Matrix J J ℂ)
    (hU : star U * U = 1) : IsEffect (star U * P * U) := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hP.1.conjTranspose_mul_mul_same U
  · have h := hP.2.conjTranspose_mul_mul_same U
    have e : Uᴴ * (1 - P) * U = 1 - star U * P * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hU]
    rwa [e] at h

/-- Effects have trace pairing with a Hermitian bounded by the trace norm. -/
theorem effect_le_traceNorm {P H : Matrix J J ℂ} (hP : IsEffect P) (hH : H.IsHermitian) :
    (P * H).trace.re ≤ traceNorm H := by
  set U : Matrix J J ℂ := (hH.eigenvectorUnitary : Matrix J J ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.eigenvectorUnitary).2
  set Q := star U * P * U
  have hQ : IsEffect Q := effect_conj hP U hU
  have e : (P * H).trace = (Q * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))).trace := by
    conv_lhs => rw [spec hH]
    simp only [Q, U]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [e, traceNorm_herm hH]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h0 : 0 ≤ Q i i := hQ.1.diag_nonneg
  have h1 : 0 ≤ (1 - Q) i i := hQ.2.diag_nonneg
  have h0' := Complex.nonneg_iff.mp h0
  have h1' := Complex.nonneg_iff.mp h1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h1'
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp at h1'
  rcases le_total 0 (hH.eigenvalues i) with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

end X6D21


noncomputable section

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B P : QAlgorithms.Papers.Independent.Information100.P63.Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hP : IsEffect P) (eps : ℝ) (heps : 0 < eps) (hd : traceNorm (A - B) ≤ eps) :
    QAlgorithms.Papers.Independent.Dependency50.P35.tr (P * (A - B)) ≤ eps :=
  le_trans (X6D21.effect_le_traceNorm hP (hA.sub hB)) hd
