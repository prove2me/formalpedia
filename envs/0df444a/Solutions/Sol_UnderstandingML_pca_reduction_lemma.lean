-- Prove2me | solution 1 for UnderstandingML.pca_reduction_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T14:08:39.083647+00:00
-- url     : https://prove2.me/submissions/10101a43-d091-43e3-9e81-5bd73f1131e8

import Definitions.Def_UnderstandingML_DimReduction
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory InnerProductSpace

namespace UnderstandingML.PCAReductionAux

variable {m d n : ℕ}

lemma sqNorm_eq_dot (v : Fin d → ℝ) : sqNorm v = v ⬝ᵥ v := by
  simp [sqNorm, dotProduct, sq]

/-- If `VᵀV = I`, then `x − VVᵀx` is the closest point of the column space of `V` to `x`. -/
lemma proj_le (V : Matrix (Fin d) (Fin n) ℝ) (hV : V.transpose * V = 1)
    (x : Fin d → ℝ) (c : Fin n → ℝ) :
    sqNorm (x - V.mulVec (V.transpose.mulVec x)) ≤ sqNorm (x - V.mulVec c) := by
  set p := x - V.mulVec (V.transpose.mulVec x) with hp
  set q := V.mulVec (V.transpose.mulVec x - c) with hq
  have hsum : x - V.mulVec c = p + q := by
    simp only [hp, hq, Matrix.mulVec_sub]; abel
  have hVp : V.transpose.mulVec p = 0 := by
    simp [hp, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV]
  have hpq : p ⬝ᵥ q = 0 := by
    rw [hq, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hVp, zero_dotProduct]
  rw [hsum, sqNorm_eq_dot, sqNorm_eq_dot]
  have : (p + q) ⬝ᵥ (p + q) = p ⬝ᵥ p + 2 * (p ⬝ᵥ q) + q ⬝ᵥ q := by
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm q p]; ring
  rw [this, hpq]
  have : 0 ≤ q ⬝ᵥ q := by
    rw [← sqNorm_eq_dot]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

/-- An orthonormal `V ∈ ℝ^{d×n}` whose column space contains that of a given `U`. -/
lemma exists_orthonormal_span (hn : n ≤ d) (U : Matrix (Fin d) (Fin n) ℝ) :
    ∃ V : Matrix (Fin d) (Fin n) ℝ, V.transpose * V = 1 ∧ V * V.transpose * U = U := by
  classical
  let f : Fin d → EuclideanSpace ℝ (Fin d) := fun j =>
    if h : j.val < n then WithLp.toLp 2 (fun k => U k ⟨j.val, h⟩) else 0
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d) := by simp
  let b := gramSchmidtOrthonormalBasis hcard f
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin d) (Fin n) ℝ, ∀ k j, V k j = b (Fin.castLE hn j) k :=
    ⟨Matrix.of fun k j => b (Fin.castLE hn j) k, fun _ _ => rfl⟩
  have horth := b.orthonormal
  rw [orthonormal_iff_ite] at horth
  refine ⟨V, ?_, ?_⟩
  · refine Matrix.ext (fun i j => ?_)
    have := horth (Fin.castLE hn i) (Fin.castLE hn j)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hVdef]
    simp only [Fin.castLE_inj] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  · refine Matrix.ext (fun k j => ?_)
    -- expansion of the `j`-th column of `U` in the basis `b`
    have hexp := b.sum_repr' (f (Fin.castLE hn j))
    have hfj : f (Fin.castLE hn j) = WithLp.toLp 2 (fun k => U k j) := by
      simp [f, j.isLt]
    have hzero : ∀ i : Fin d, n ≤ i.val →
        inner ℝ (b i) (f (Fin.castLE hn j)) = 0 := by
      intro i hi
      apply gramSchmidtOrthonormalBasis_inv_triangular
      show (Fin.castLE hn j) < i
      rw [Fin.lt_def]; simp; omega
    have hsplit : ∑ i : Fin d, inner ℝ (b i) (f (Fin.castLE hn j)) • b i =
        ∑ l : Fin n, inner ℝ (b (Fin.castLE hn l)) (f (Fin.castLE hn j)) • b (Fin.castLE hn l) := by
      have hmap : ∑ l : Fin n, inner ℝ (b (Fin.castLE hn l)) (f (Fin.castLE hn j)) •
          b (Fin.castLE hn l) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hn),
          inner ℝ (b i) (f (Fin.castLE hn j)) • b i := by
        rw [Finset.sum_map]; rfl
      rw [hmap]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have : n ≤ i.val := by
        by_contra hlt
        push Not at hlt
        apply hi
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        exact ⟨⟨i.val, hlt⟩, rfl⟩
      rw [hzero i this, zero_smul]
    rw [hsplit, hfj] at hexp
    have hk := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v k) hexp
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hk
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hVdef, Finset.sum_mul]
    rw [← hk]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

end UnderstandingML.PCAReductionAux

open UnderstandingML UnderstandingML.PCAReductionAux in
theorem solution {m d n : ℕ} (hn : n ≤ d) (x : Fin m → Fin d → ℝ)
    (U : Matrix (Fin d) (Fin n) ℝ) (W : Matrix (Fin n) (Fin d) ℝ) :
    ∃ V : Matrix (Fin d) (Fin n) ℝ, V.transpose * V = 1 ∧
      pcaObjective x V V.transpose ≤ pcaObjective x U W := by
  obtain ⟨V, hV, hVU⟩ := exists_orthonormal_span hn U
  refine ⟨V, hV, ?_⟩
  unfold pcaObjective
  apply Finset.sum_le_sum
  intro i _
  have : U.mulVec (W.mulVec (x i)) = V.mulVec (V.transpose.mulVec (U.mulVec (W.mulVec (x i)))) := by
    simp only [Matrix.mulVec_mulVec]; rw [← Matrix.mul_assoc V V.transpose (U * W), ← Matrix.mul_assoc (V * V.transpose) U W, hVU]
  rw [this]
  exact proj_le V hV (x i) _
