-- Prove2me | solution 1 for UnderstandingML.pca_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:21:43.807239+00:00
-- url     : https://prove2.me/submissions/dfd57faa-a32d-4acb-b0eb-52f6b7e0ba3e

import Definitions.Def_UnderstandingML_DimReduction
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace

open MeasureTheory ProbabilityTheory

namespace UnderstandingML.PCATheoremAux

open InnerProductSpace

variable {m d n : ℕ}

lemma sqNorm_eq_dot (v : Fin d → ℝ) : sqNorm v = v ⬝ᵥ v := by
  simp [sqNorm, dotProduct, sq]

/-- Squared row norms of a matrix. -/
def rowSq (B : Matrix (Fin d) (Fin n) ℝ) (j : Fin d) : ℝ := ∑ k, B j k ^ 2

lemma rowSq_nonneg (B : Matrix (Fin d) (Fin n) ℝ) (j : Fin d) : 0 ≤ rowSq B j :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma rowSq_le_one (B : Matrix (Fin d) (Fin n) ℝ) (hB : B.transpose * B = 1) (j : Fin d) :
    rowSq B j ≤ 1 := by
  set P := B * B.transpose with hP
  have hPP : P * P = P := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc B.transpose, hB, Matrix.one_mul]
  have hjj : P j j = rowSq B j := by
    simp [hP, rowSq, Matrix.mul_apply, sq]
  have hsym : ∀ l, P l j = P j l := by
    intro l; simp [hP, Matrix.mul_apply, mul_comm]
  have hsq : P j j = ∑ l, P j l ^ 2 := by
    conv_lhs => rw [← hPP]
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun l _ => by rw [hsym l, sq])
  have hge : P j j ^ 2 ≤ P j j := by
    have := Finset.single_le_sum (f := fun l => P j l ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
    rw [← hsq] at this
    exact this
  have h0 : 0 ≤ P j j := hjj ▸ rowSq_nonneg B j
  rw [← hjj]; nlinarith

lemma sum_rowSq (B : Matrix (Fin d) (Fin n) ℝ) (hB : B.transpose * B = 1) :
    ∑ j, rowSq B j = n := by
  have h := congrArg Matrix.trace hB
  simp only [Matrix.trace_one, Fintype.card_fin] at h
  rw [← h]
  simp only [rowSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp [sq]

/-- The rearrangement step: weights in `[0,1]` summing to `n` give at most the sum of the
`n` largest values of a nonincreasing sequence. -/
lemma weighted_le_top (hn : n ≤ d) (D : Fin d → ℝ) (hD : Antitone D) (β : Fin d → ℝ)
    (h0 : ∀ j, 0 ≤ β j) (h1 : ∀ j, β j ≤ 1) (hs : ∑ j, β j = n) :
    ∑ j, D j * β j ≤ ∑ j, D j * (if j.val < n then 1 else 0) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  set c := D ⟨n - 1, by omega⟩
  have key : ∀ j : Fin d, (D j - c) * (β j - if j.val < n then 1 else 0) ≤ 0 := by
    intro j
    split_ifs with hj
    · have : c ≤ D j := hD (show j ≤ ⟨n - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
      nlinarith [h1 j]
    · have : D j ≤ c := hD (show (⟨n - 1, by omega⟩ : Fin d) ≤ j from Fin.le_def.mpr (by simp; omega))
      nlinarith [h0 j]
  have hsum : ∑ j : Fin d, (if j.val < n then (1:ℝ) else 0) = n := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    norm_cast
    have : (Finset.univ.filter (fun j : Fin d => j.val < n)) = Finset.univ.map (Fin.castLEEmb hn) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨⟨j.val, h⟩, rfl⟩
      · rintro ⟨k, rfl⟩; simp
    rw [this, Finset.card_map]; simp
  have h2 := Finset.sum_nonpos (s := Finset.univ) (fun j _ => key j)
  have h3 : ∑ j, (D j - c) * (β j - if j.val < n then 1 else 0) =
      ∑ j, D j * β j - ∑ j, D j * (if j.val < n then 1 else 0)
        - c * (∑ j, β j - ∑ j : Fin d, (if j.val < n then (1:ℝ) else 0)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hs, hsum, sub_self, mul_zero, sub_zero] at h3
  linarith

/-- For orthonormal `Q`, `‖x − QQᵀx‖² = ‖x‖² − ‖Qᵀx‖²`. -/
lemma sqNorm_sub_proj (Q : Matrix (Fin d) (Fin n) ℝ) (hQ : Q.transpose * Q = 1)
    (v : Fin d → ℝ) :
    sqNorm (v - Q.mulVec (Q.transpose.mulVec v)) = sqNorm v - sqNorm (Q.transpose.mulVec v) := by
  set y := Q.transpose.mulVec v
  rw [sqNorm_eq_dot, sqNorm_eq_dot, sqNorm_eq_dot]
  have h1 : v ⬝ᵥ Q.mulVec y = y ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have h2 : Q.mulVec y ⬝ᵥ Q.mulVec y = y ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
      Matrix.one_mulVec]
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (Q.mulVec y) v, h1, h2]
  ring

/-- `∑ᵢ ‖Qᵀxᵢ‖² = ∑ⱼ Dⱼ ‖(VᵀQ)ⱼ‖²`. -/
lemma sum_sqNorm_proj (x : Fin m → Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ) (D : Fin d → ℝ)
    (hA : scatterMatrix x = V * Matrix.diagonal D * V.transpose)
    (Q : Matrix (Fin d) (Fin n) ℝ) :
    ∑ i, sqNorm (Q.transpose.mulVec (x i)) = ∑ j, D j * rowSq (V.transpose * Q) j := by
  have hq : ∀ v : Fin d → ℝ, sqNorm (Q.transpose.mulVec v) =
      Matrix.trace (Q * Q.transpose * Matrix.vecMulVec v v) := by
    intro v
    simp only [sqNorm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Matrix.vecMulVec_apply, sq, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => arg 2; ext c; rw [Finset.sum_comm]
    rw [Finset.sum_comm (f := fun c k => ∑ e, _)]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro l' _
    ring
  simp only [hq]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum]
  change Matrix.trace (Q * Q.transpose * scatterMatrix x) = _
  rw [hA]
  have : Q * Q.transpose * (V * Matrix.diagonal D * V.transpose) =
      (Q * Q.transpose * V) * (Matrix.diagonal D * V.transpose) := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, rowSq,
    Matrix.transpose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    sq, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun y i => ∑ x, _)]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro l' _
  ring

lemma obj_orth (x : Fin m → Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ) (D : Fin d → ℝ)
    (hA : scatterMatrix x = V * Matrix.diagonal D * V.transpose)
    (Q : Matrix (Fin d) (Fin n) ℝ) (hQ : Q.transpose * Q = 1) :
    pcaObjective x Q Q.transpose =
      ∑ i, sqNorm (x i) - ∑ j, D j * rowSq (V.transpose * Q) j := by
  unfold pcaObjective
  rw [← sum_sqNorm_proj x V D hA Q, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => sqNorm_sub_proj Q hQ (x i))

lemma rowSq_top (hn : n ≤ d) (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (j : Fin d) :
    rowSq (V.transpose * V.submatrix id (Fin.castLE hn)) j = if j.val < n then 1 else 0 := by
  have hcol : V.transpose * V.submatrix id (Fin.castLE hn) =
      (1 : Matrix (Fin d) (Fin d) ℝ).submatrix id (Fin.castLE hn) := by
    rw [← hV]; rfl
  rw [hcol]
  simp only [rowSq, Matrix.submatrix_apply, id, Matrix.one_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · simp
    · intro k _ hk
      rw [if_neg]; · simp
      intro h; apply hk; ext; simp [h]
    · simp
  · apply Finset.sum_eq_zero; intro k _
    rw [if_neg]; · simp
    intro h; apply hj; rw [h]; simp

lemma top_orth (hn : n ≤ d) (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.transpose * V = 1) :
    (V.submatrix id (Fin.castLE hn)).transpose * V.submatrix id (Fin.castLE hn) = 1 := by
  have : (V.submatrix id (Fin.castLE hn)).transpose * V.submatrix id (Fin.castLE hn) =
      (V.transpose * V).submatrix (Fin.castLE hn) (Fin.castLE hn) := by
    ext i j; simp [Matrix.mul_apply]
  rw [this, hV]
  ext i j
  simp [Matrix.one_apply, Fin.ext_iff]

lemma orth_comp (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.transpose * V = 1)
    (Q : Matrix (Fin d) (Fin n) ℝ) (hQ : Q.transpose * Q = 1) :
    (V.transpose * Q).transpose * (V.transpose * Q) = 1 := by
  have hV' : V * V.transpose = 1 := mul_eq_one_comm.mp hV
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc V, hV', Matrix.one_mul, hQ]

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

/-- Lemma 23.1: reduction to orthonormal `U` and `W = Uᵀ`. -/
lemma pca_reduction (hn : n ≤ d) (x : Fin m → Fin d → ℝ)
    (U : Matrix (Fin d) (Fin n) ℝ) (W : Matrix (Fin n) (Fin d) ℝ) :
    ∃ Q : Matrix (Fin d) (Fin n) ℝ, Q.transpose * Q = 1 ∧
      pcaObjective x Q Q.transpose ≤ pcaObjective x U W := by
  obtain ⟨V, hV, hVU⟩ := exists_orthonormal_span hn U
  refine ⟨V, hV, ?_⟩
  unfold pcaObjective
  apply Finset.sum_le_sum
  intro i _
  have : U.mulVec (W.mulVec (x i)) =
      V.mulVec (V.transpose.mulVec (U.mulVec (W.mulVec (x i)))) := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc V V.transpose (U * W), ← Matrix.mul_assoc (V * V.transpose) U W, hVU]
  rw [this]
  exact proj_le V hV (x i) _

end UnderstandingML.PCATheoremAux

open UnderstandingML UnderstandingML.PCATheoremAux in
/-- **Theorem 23.2** (p. 325). -/
theorem solution {m d n : ℕ} (hn : n ≤ d) (x : Fin m → Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.transpose * V = 1) (D : Fin d → ℝ) (hD : Antitone D)
    (hA : scatterMatrix x = V * Matrix.diagonal D * V.transpose)
    (U : Matrix (Fin d) (Fin n) ℝ) (W : Matrix (Fin n) (Fin d) ℝ) :
    pcaObjective x (V.submatrix id (Fin.castLE hn)) (V.submatrix id (Fin.castLE hn)).transpose ≤
      pcaObjective x U W := by
  obtain ⟨Q, hQ, hQle⟩ := pca_reduction hn x U W
  refine le_trans ?_ hQle
  rw [obj_orth x V D hA _ (top_orth hn V hV), obj_orth x V D hA Q hQ]
  simp only [rowSq_top hn V hV]
  have := weighted_le_top hn D hD _ (rowSq_nonneg _) (rowSq_le_one _ (orth_comp V hV Q hQ))
    (sum_rowSq _ (orth_comp V hV Q hQ))
  linarith

