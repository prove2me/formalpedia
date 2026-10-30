-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.stabilizerConstraintEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:22:37.784881+00:00
-- url     : https://prove2.me/submissions/9c059992-1ba4-4850-8812-d71588ef9af6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

lemma trN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A.conjTranspose * A) = (frobSq A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, frobSq]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp

lemma frobSq_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : frobSq A = 0) : A = 0 := by
  unfold frobSq at h
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => ∑ j, Complex.normSq (A i j))
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).mp h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun j => Complex.normSq (A i j)) (fun j _ => Complex.normSq_nonneg _)).mp
    (h' i (Finset.mem_univ i)) j (Finset.mem_univ j)
  simpa using h1

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {n : ℕ} (hn : 0 < n) (E : (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : (Matrix (Fin n) (Fin n) ℂ)) * E * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose = E ↔
      Matrix.trace (E.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * E * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose)) -
        (frobSq E : ℂ) = 0 := by
  set V : Matrix (Fin n) (Fin n) ℂ := (U : Matrix (Fin n) (Fin n) ℂ) * E * (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose with hV
  constructor
  · intro h
    rw [h, trN]; ring
  · intro h
    have hU : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp U.2
      simpa [Matrix.star_eq_conjTranspose] using this
    have e : ∀ X : Matrix (Fin n) (Fin n) ℂ, (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((U : Matrix (Fin n) (Fin n) ℂ) * X) = X := by
      intro X; rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    have h1 : Matrix.trace (V.conjTranspose * V) = Matrix.trace (E.conjTranspose * E) := by
      have : V.conjTranspose * V = (U : Matrix (Fin n) (Fin n) ℂ) * (E.conjTranspose * E) *
          (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
        rw [hV]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        rw [e]
      rw [this, Matrix.trace_mul_comm, e]
    have h2 : Matrix.trace (E.conjTranspose * V) = (frobSq E : ℂ) := by
      rw [sub_eq_zero] at h; exact h
    have h3 : Matrix.trace (V.conjTranspose * E) = (frobSq E : ℂ) := by
      have : V.conjTranspose * E = (E.conjTranspose * V).conjTranspose := by
        simp [Matrix.conjTranspose_mul]
      rw [this, Matrix.trace_conjTranspose, h2]
      simp
    have h4 : Matrix.trace ((V - E).conjTranspose * (V - E)) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
      rw [h1, h2, h3, trN]; ring
    rw [trN] at h4
    have h5 : frobSq (V - E) = 0 := by exact_mod_cast h4
    exact sub_eq_zero.mp (frobSq_eq_zero _ h5)
