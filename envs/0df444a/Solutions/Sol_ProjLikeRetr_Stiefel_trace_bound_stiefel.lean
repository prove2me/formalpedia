-- Prove2me | solution 1 for ProjLikeRetr.Stiefel.trace_bound_stiefel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:02:38.06875+00:00
-- url     : https://prove2.me/submissions/a168397e-c941-4e73-abc6-1b4688c08f64

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ProjLikeRetr_Stiefel_SVD

open scoped Matrix

namespace P9ed9c518

lemma orth_tt {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (h : U ∈ Matrix.orthogonalGroup (Fin k) ℝ) : Uᵀ * U = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma orth_t {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (h : U ∈ Matrix.orthogonalGroup (Fin k) ℝ) : U * Uᵀ = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma diag_sum {n m : ℕ} (hmn : m ≤ n) (S : Matrix (Fin n) (Fin m) ℝ)
    (hS : ∀ i j, i.val ≠ j.val → S i j = 0) (A : Matrix (Fin m) (Fin n) ℝ) :
    (A * S).trace = ∑ j : Fin m, A j (Fin.castLE hmn j) * S (Fin.castLE hmn j) j := by
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_eq_single (Fin.castLE hmn j) ?_ ?_
  · intro i _ hi
    have : i.val ≠ j.val := fun h => hi (Fin.ext (by simp [h]))
    simp [hS i j this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma entry_le_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : A * Aᵀ = 1)
    (j : Fin m) (i : Fin n) : A j i ≤ 1 := by
  have h1 : ∑ k, A j k * A j k = 1 := by
    have := congrFun (congrFun h j) j
    simpa [Matrix.mul_apply] using this
  have h2 : A j i * A j i ≤ ∑ k, A j k * A j k :=
    Finset.single_le_sum (f := fun k => A j k * A j k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  nlinarith

lemma rect_tt {n m : ℕ} (hmn : m ≤ n) :
    (ProjLikeRetr.Stiefel.rectId n m)ᵀ * ProjLikeRetr.Stiefel.rectId n m = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ProjLikeRetr.Stiefel.rectId,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castLE hmn i)]
  · by_cases hij : i = j
    · subst hij; simp
    · have : ¬ ((Fin.castLE hmn i).val = j.val) := by
        simpa [Fin.ext_iff] using hij
      simp only [this, if_false, mul_zero]
      simp only [Fin.ext_iff] at hij
      simp [Fin.ext_iff, hij]
  · intro k _ hk
    have : ¬ (k.val = i.val) := fun h => hk (Fin.ext (by simp [h]))
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end P9ed9c518

open ProjLikeRetr.Stiefel Matrix in
theorem solution {n m : ℕ} (hmn : m ≤ n) (X : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hsvd : ProjLikeRetr.FixedRank.IsSVD X U S V) :
    (∀ Y ∈ stiefel n m, (Yᵀ * X).trace ≤ ∑ i : Fin m, S (Fin.castLE hmn i) i) ∧
      frameOfSVD U V ∈ stiefel n m ∧
      ((frameOfSVD U V)ᵀ * X).trace = ∑ i : Fin m, S (Fin.castLE hmn i) i := by
  obtain ⟨hU, hV, hoff, hnn, -, hX⟩ := hsvd
  have hUtU := P9ed9c518.orth_tt hU
  have hUUt := P9ed9c518.orth_t hU
  have hVtV := P9ed9c518.orth_tt hV
  have hVVt := P9ed9c518.orth_t hV
  have hE := P9ed9c518.rect_tt hmn
  refine ⟨?_, ?_, ?_⟩
  · intro Y hY
    have hY' : Yᵀ * Y = 1 := hY
    have htr : (Yᵀ * X).trace = ((Vᵀ * Yᵀ * U) * S).trace := by
      rw [hX]
      calc (Yᵀ * (U * S * Vᵀ)).trace = ((Yᵀ * U * S) * Vᵀ).trace := by
              simp only [Matrix.mul_assoc]
        _ = (Vᵀ * (Yᵀ * U * S)).trace := Matrix.trace_mul_comm _ _
        _ = ((Vᵀ * Yᵀ * U) * S).trace := by simp only [Matrix.mul_assoc]
    rw [htr, P9ed9c518.diag_sum hmn S hoff]
    have hA : (Vᵀ * Yᵀ * U) * (Vᵀ * Yᵀ * U)ᵀ = 1 := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᵀ, hUUt, Matrix.one_mul, ← Matrix.mul_assoc Yᵀ Y, hY',
        Matrix.one_mul, hVtV]
    apply Finset.sum_le_sum
    intro j _
    have h1 := P9ed9c518.entry_le_one _ hA j (Fin.castLE hmn j)
    have h2 : 0 ≤ S (Fin.castLE hmn j) j := hnn _ _ (by simp)
    nlinarith
  · show (frameOfSVD U V)ᵀ * frameOfSVD U V = 1
    unfold frameOfSVD
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul, ← Matrix.mul_assoc (rectId n m)ᵀ,
      hE, Matrix.one_mul, hVVt]
  · rw [hX]
    unfold frameOfSVD
    have : ((U * rectId n m * Vᵀ)ᵀ * (U * S * Vᵀ)).trace = ((rectId n m)ᵀ * S).trace := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul, Matrix.trace_mul_comm V]
      simp only [Matrix.mul_assoc, hVtV, Matrix.mul_one]
    rw [this, P9ed9c518.diag_sum hmn S hoff]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [rectId]
