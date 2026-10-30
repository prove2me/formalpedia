-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P40.lemma2_unitary_hermitian_trace_separates
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:16:47.925064+00:00
-- url     : https://prove2.me/submissions/e699b281-067a-4b15-bbc6-ad54982f1734

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

lemma refl_mem {n : ℕ} (w : Fin n → ℂ) (hw : star w ⬝ᵥ w = 2) :
    (1 - Matrix.vecMulVec w (star w) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    (1 - Matrix.vecMulVec w (star w) : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
  have hH : (1 - Matrix.vecMulVec w (star w) : Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.one_apply, eq_comm, mul_comm]
  have hsq : (1 - Matrix.vecMulVec w (star w) : Matrix (Fin n) (Fin n) ℂ) *
      (1 - Matrix.vecMulVec w (star w)) = 1 := by
    have h2 : Matrix.vecMulVec w (star w) * Matrix.vecMulVec w (star w) =
        (2 : ℂ) • Matrix.vecMulVec w (star w) := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hw, Matrix.vecMulVec_smul]
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, h2]
    ext i j
    simp [two_smul]
  refine ⟨?_, hH⟩
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, hH.eq]
  exact hsq

open Matrix in
lemma trace_Q {n : ℕ} (w : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((1 - Matrix.vecMulVec w (star w) : Matrix (Fin n) (Fin n) ℂ) * X) =
      Matrix.trace X - star w ⬝ᵥ Matrix.mulVec X w := by
  rw [sub_mul, Matrix.trace_sub, Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  simp [Matrix.trace, Matrix.vecMul, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm]
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

lemma Q_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ A : Matrix.unitaryGroup (Fin n) ℂ,
      (A : Matrix (Fin n) (Fin n) ℂ).IsHermitian → Matrix.trace ((A : Matrix (Fin n) (Fin n) ℂ) * X) = 0)
    (w : Fin n → ℂ) (hw : star w ⬝ᵥ w = 2) : star w ⬝ᵥ Matrix.mulVec X w = 0 := by
  have h1 := htrace 1 (by simp)
  simp at h1
  obtain ⟨hm, hh⟩ := refl_mem w hw
  have h2 := htrace ⟨_, hm⟩ hh
  simp only [trace_Q] at h2
  rw [h1] at h2
  simpa using h2

lemma Q_one {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (w : Fin n → ℂ)
    (hw : ∀ a, a ≠ i → w a = 0) :
    star w ⬝ᵥ Matrix.mulVec X w = star (w i) * (X i i * w i) := by
  have hin : Matrix.mulVec X w i = X i i * w i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · intro b _ hb; rw [hw b hb]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
  simp only [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [hin]
  · intro b _ hb; simp [hw b hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma Q_two {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j) (w : Fin n → ℂ)
    (hw : ∀ a, a ≠ i → a ≠ j → w a = 0) :
    star w ⬝ᵥ Matrix.mulVec X w =
      star (w i) * (X i i * w i + X i j * w j) + star (w j) * (X j i * w i + X j j * w j) := by
  have hin : ∀ r, Matrix.mulVec X w r = X r i * w i + X r j * w j := by
    intro r
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_eq_add i j hij (fun b _ hb => by rw [hw b hb.1 hb.2]; simp)
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)
  simp only [dotProduct]
  rw [Finset.sum_eq_add i j hij (fun b _ hb => by simp [hw b hb.1 hb.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h), hin, hin]
  simp

lemma Q_diag {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (h : ∀ w : Fin n → ℂ, star w ⬝ᵥ w = 2 → star w ⬝ᵥ Matrix.mulVec X w = 0) : X i i = 0 := by
  have h2 : star (fun a : Fin n => if a = i then (Real.sqrt 2 : ℂ) else 0) ⬝ᵥ
      (fun a : Fin n => if a = i then (Real.sqrt 2 : ℂ) else 0) = 2 := by
    simp only [dotProduct]
    rw [Finset.sum_eq_single i]
    · simp
      rw [← Complex.ofReal_mul]; simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  have := h _ h2
  rw [Q_one X i _ (fun a ha => by simp [ha])] at this
  simp at this
  exact this

lemma Q_off {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j) (c : ℂ) (hc : starRingEnd ℂ c * c = 1)
    (h : ∀ w : Fin n → ℂ, star w ⬝ᵥ w = 2 → star w ⬝ᵥ Matrix.mulVec X w = 0) :
    X i i + X j j + starRingEnd ℂ c * X j i + c * X i j = 0 := by
  have hw : ∀ a, a ≠ i → a ≠ j → (fun a : Fin n => if a = i then (1:ℂ) else if a = j then c else 0) a = 0 := by
    intro a h1 h2; simp [h1, h2]
  have h2 : star (fun a : Fin n => if a = i then (1:ℂ) else if a = j then c else 0) ⬝ᵥ
      (fun a : Fin n => if a = i then (1:ℂ) else if a = j then c else 0) = 2 := by
    simp only [dotProduct]
    rw [Finset.sum_eq_add i j hij (fun b _ hb => by simp [hb.1, hb.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
    simp [hij.symm]
    linear_combination hc
  have := h _ h2
  rw [Q_two X i j hij _ hw] at this
  simp [hij.symm] at this
  linear_combination this - X j j * hc

end QAlgorithms.Papers.Independent.Advance50.P40

open QAlgorithms.Papers.Independent.Advance50.P40 in
/-- Lemma 2: unitary Hermitian trace pairing separates matrices. -/
theorem solution {n : ℕ} [NeZero n]
    (X : SystemMatrix n)
    (htrace : ∀ A : Matrix.unitaryGroup (Fin n) ℂ,
      (A : SystemMatrix n).IsHermitian →
        Matrix.trace ((A : SystemMatrix n) * X) = 0) :
    X = 0 := by
  have hQ := Q_zero X htrace
  ext i j
  by_cases hij : i = j
  · subst hij; simpa using Q_diag X i hQ
  · have d1 := Q_diag X i hQ
    have d2 := Q_diag X j hQ
    have e1 := Q_off X i j hij 1 (by simp) hQ
    have e2 := Q_off X i j hij Complex.I (by simp) hQ
    simp at e1 e2
    rw [d1, d2] at e1 e2
    simp
    have : (2 : ℂ) * X i j = 0 := by linear_combination e1 - Complex.I * e2 + (X i j - X j i) * Complex.I_sq
    simpa using this
