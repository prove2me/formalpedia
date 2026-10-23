-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.coherenceGenerationMatrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:08.163526+00:00
-- url     : https://prove2.me/submissions/91f65082-4178-48ca-a33d-fba80f408e38

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7G_row {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (i : ι) : ∑ j, transition U i j = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def,
    Complex.mul_conj] at h
  simp only [transition]
  exact_mod_cast h

lemma X7G_col {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (j : ι) : ∑ i, transition U i j = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def,
    mul_comm (conj _), Complex.mul_conj] at h
  simp only [transition]
  exact_mod_cast h

lemma X7G_frob {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    ∑ l, ∑ m, Complex.normSq (X l m) = ((Xᴴ * X).trace).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma X7G_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (p : ι → ℝ)
    (l m : ι) : conjSuperop U (inputDensity p) l m = ∑ k, U l k * (p k : ℂ) * conj (U m k) := by
  simp only [conjSuperop, inputDensity, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]

lemma X7G_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (p : ι → ℝ)
    (i : ι) : conjSuperop U (inputDensity p) i i = (((transition U).mulVec p i : ℝ) : ℂ) := by
  rw [X7G_entry]
  simp only [Matrix.mulVec, dotProduct, transition, Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_right_comm, Complex.mul_conj]

lemma X7G_offsum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (l : ι) :
    (∑ m, if l = m then 0 else f m) = ∑ m, f m - f l := by
  rw [show (∑ m, if l = m then 0 else f m) = ∑ m, (f m - if l = m then f m else 0) from
    Finset.sum_congr rfl fun m _ => by split_ifs <;> simp]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

lemma X7G_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic G x = x ⬝ᵥ G.mulVec x := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma X7G_form {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (x : ι → ℝ) :
    x ⬝ᵥ (response U).mulVec x = x ⬝ᵥ x - (transition U).mulVec x ⬝ᵥ (transition U).mulVec x := by
  rw [response, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let P := transition U
    let G := response U
    G.IsSymm ∧ G.PosSemidef ∧ (1 - G).PosSemidef ∧
    G.mulVec (fun _ => 1) = 0 ∧ P.mulVec (fun _ => 1) = (fun _ => 1) ∧
    Pᵀ.mulVec (fun _ => 1) = (fun _ => 1) ∧
    ∀ p, IsPopulation p →
      generated (conjSuperop U) p = quadratic G p ∧
      quadratic G p = quadratic G (centered p) ∧
      (∀ i, (conjSuperop U (inputDensity p) i i).re = (P.mulVec p) i) := by
  intro P G
  have hsym : Gᵀ = G := by
    simp [G, response, Matrix.transpose_sub, Matrix.transpose_mul]
  have hP1 : P.mulVec (fun _ => 1) = (fun _ => 1) := by
    ext i; simp [Matrix.mulVec, dotProduct, P, X7G_row U hU i]
  have hPT1 : Pᵀ.mulVec (fun _ => 1) = (fun _ => 1) := by
    ext i; simp [Matrix.mulVec, dotProduct, P, X7G_col U hU i]
  have hG1 : G.mulVec (fun _ => 1) = 0 := by
    simp only [G, response, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    change (fun _ => (1:ℝ)) - Pᵀ.mulVec (P.mulVec fun _ => 1) = 0
    rw [hP1, hPT1, sub_self]
  have hHerm : G.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hsym]
  refine ⟨hsym, ?_, ?_, hG1, hP1, hPT1, ?_⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hHerm, fun x => ?_⟩
    simp only [star_trivial]
    rw [X7G_form, sub_nonneg]
    have hj : ∀ i, (P.mulVec x i) ^ 2 ≤ ∑ j, P i j * x j ^ 2 := by
      intro i
      have := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).map_sum_le
        (t := Finset.univ) (w := fun j => P i j) (p := x)
        (fun j _ => Complex.normSq_nonneg _) (X7G_row U hU i) (fun _ _ => Set.mem_univ _)
      simpa [Matrix.mulVec, dotProduct, smul_eq_mul] using this
    calc P.mulVec x ⬝ᵥ P.mulVec x = ∑ i, (P.mulVec x i) ^ 2 := by
          simp [dotProduct, sq]
      _ ≤ ∑ i, ∑ j, P i j * x j ^ 2 := Finset.sum_le_sum fun i _ => hj i
      _ = ∑ j, x j ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, X7G_col U hU j, one_mul]
      _ = x ⬝ᵥ x := by simp [dotProduct, sq]
  · have : (1 : Matrix ι ι ℝ) - G = Pᵀ * P := by simp [G, response, P]
    rw [this, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.posSemidef_conjTranspose_mul_self P
  · intro p _
    refine ⟨?_, ?_, ?_⟩
    · have hfull : ∑ l, ∑ m, Complex.normSq (conjSuperop U (inputDensity p) l m) = ∑ k, p k ^ 2 := by
        rw [X7G_frob]
        have hUU : Uᴴ * U = 1 := by
          rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
        have : (conjSuperop U (inputDensity p))ᴴ * conjSuperop U (inputDensity p) =
            U * ((inputDensity p)ᴴ * inputDensity p) * Uᴴ := by
          simp only [conjSuperop, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
        rw [this, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
        simp [inputDensity, Matrix.trace, Matrix.diagonal_conjTranspose, Complex.re_sum, sq]
      have hdiag : ∀ l, Complex.normSq (conjSuperop U (inputDensity p) l l) = (P.mulVec p l) ^ 2 := by
        intro l; rw [X7G_diag, Complex.normSq_ofReal, sq]
      have hcoh : generated (conjSuperop U) p = ∑ l, ∑ m,
          Complex.normSq (conjSuperop U (inputDensity p) l m) -
          ∑ l, Complex.normSq (conjSuperop U (inputDensity p) l l) := by
        simp only [generated, coherence]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact X7G_offsum _ l
      rw [hcoh, hfull, X7G_quad, X7G_form]
      simp only [hdiag, dotProduct, sq]
      rfl
    · rw [X7G_quad, X7G_quad]
      have hc : centered p = p - fun _ => 1 / (Fintype.card ι : ℝ) := rfl
      have hc' : (fun _ : ι => 1 / (Fintype.card ι : ℝ)) = (1 / (Fintype.card ι : ℝ)) • fun _ => 1 := by
        ext; simp
      have hG1' : (fun _ : ι => (1:ℝ)) ᵥ* G = 0 := by
        rw [← Matrix.mulVec_transpose, hsym, hG1]
      rw [hc, hc', Matrix.mulVec_sub, Matrix.mulVec_smul, hG1, smul_zero, sub_zero,
        sub_dotProduct, smul_dotProduct, Matrix.dotProduct_mulVec (fun _ => (1:ℝ)) G p, hG1', zero_dotProduct,
        smul_zero, sub_zero]
    · intro i
      rw [X7G_diag, Complex.ofReal_re]
