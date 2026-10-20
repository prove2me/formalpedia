-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P80.projectiveNorm_dimensionBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:47:46.832017+00:00
-- url     : https://prove2.me/submissions/65921acf-e200-4fb7-bc0e-4b7d26bd77d2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P80

section g53i
open scoped Matrix.Norms.L2Operator

lemma g53i_coiso_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (h : Aᴴ * A = 1) : ‖A‖ ≤ 1 := by
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [h] at h1
  have h2 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)
  nlinarith [norm_nonneg A]

lemma g53i_single_le {B : Type*} [Fintype B] [DecidableEq B] (b b' : B) :
    ‖(Matrix.single b b' (1 : ℂ) : Matrix B B ℂ)‖ ≤ 1 := by
  let u : B → Matrix B (Fin 1) ℂ := fun b => Matrix.of fun c _ => if c = b then 1 else 0
  have hu : ∀ b, (u b)ᴴ * u b = 1 := by
    intro b; ext i j
    fin_cases i; fin_cases j
    simp [u, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : (Matrix.single b b' (1 : ℂ) : Matrix B B ℂ) = u b * (u b')ᴴ := by
    ext i j
    simp [u, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases hi : i = b <;> by_cases hj : j = b' <;> aesop
  rw [hs]
  calc ‖u b * (u b')ᴴ‖ ≤ ‖u b‖ * ‖(u b')ᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul (g53i_coiso_le _ (hu b)) (g53i_coiso_le _ (hu b')) (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- compression by a co-isometry on both sides -/
lemma g53i_compress_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P Q : Matrix m n ℂ) (hP : P * Pᴴ = 1) (hQ : Q * Qᴴ = 1) (Z : Matrix n n ℂ) :
    ‖P * Z * Qᴴ‖ ≤ ‖Z‖ := by
  have hP' : ‖P‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose]; apply g53i_coiso_le; simpa using hP
  have hQ' : ‖Qᴴ‖ ≤ 1 := by apply g53i_coiso_le; simpa using hQ
  calc ‖P * Z * Qᴴ‖ ≤ ‖P * Z‖ * ‖Qᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖Z‖) * 1 := mul_le_mul (Matrix.l2_opNorm_mul _ _) hQ' (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (1 * ‖Z‖) * 1 := by gcongr
    _ = ‖Z‖ := by ring

lemma g53i_sn_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    0 ≤ specNorm A := norm_nonneg (E := Matrix m n ℂ) _

lemma g53i_sn {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    specNorm A = ‖A‖ := rfl

end g53i

lemma g53i_costs_nonneg {B E : Type*} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    (Z : Matrix (B × E) (B × E) ℂ) : BddBelow (decompositionCosts Z) := by
  refine ⟨0, ?_⟩
  rintro t ⟨m, X, Y, -, rfl⟩
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (g53i_sn_nonneg _) (g53i_sn_nonneg _))

lemma g53i_reindex_cost {B E ι : Type*} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    [Fintype ι] (Z : Matrix (B × E) (B × E) ℂ) (X : ι → Matrix B B ℂ) (Y : ι → Matrix E E ℂ)
    (hZ : Z = ∑ p, Matrix.kronecker (X p) (Y p)) :
    projectiveNorm Z ≤ ∑ p, specNorm (X p) * specNorm (Y p) := by
  let e := Fintype.equivFin ι
  apply csInf_le (g53i_costs_nonneg Z)
  refine ⟨Fintype.card ι, fun j => X (e.symm j), fun j => Y (e.symm j), ?_, ?_⟩
  · rw [hZ]; exact (Equiv.sum_comp e.symm (fun p => Matrix.kronecker (X p) (Y p))).symm
  · exact (Equiv.sum_comp e.symm (fun p => specNorm (X p) * specNorm (Y p))).symm

open scoped Matrix.Norms.L2Operator in
/-- Lemma 2, PDF p.6, (18): the projective norm uses local spectral norms. -/
theorem solution
    {B E : Type*} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    [Nonempty B] [Nonempty E] (Z : Matrix (B × E) (B × E) ℂ) :
    projectiveNorm Z ≤
      (min ((Fintype.card B : ℝ) ^ 2) ((Fintype.card E : ℝ) ^ 2)) * specNorm Z := by
  -- B-side decomposition
  have hBside : projectiveNorm Z ≤ (Fintype.card B : ℝ) ^ 2 * specNorm Z := by
    let P : B → Matrix E (B × E) ℂ := fun b => Matrix.of fun e x => if x = (b, e) then 1 else 0
    have hP : ∀ b, P b * (P b)ᴴ = 1 := by
      intro b; ext e e'
      simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      split_ifs <;> simp_all
    let blk : B × B → Matrix E E ℂ := fun p => Matrix.of fun e e' => Z (p.1, e) (p.2, e')
    have hblk : ∀ p, blk p = P p.1 * Z * (P p.2)ᴴ := by
      intro p; ext e e'
      simp [blk, P, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hdec : Z = ∑ p : B × B, Matrix.kronecker (Matrix.single p.1 p.2 (1 : ℂ)) (blk p) := by
      ext x y
      simp [blk, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
        Fintype.sum_prod_type]
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun b _ hb => Finset.sum_eq_zero
          (fun c _ => if_neg (fun h => hb h.1))),
        Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun c _ hc => if_neg (fun h => hc h.2))]
      simp
    refine (g53i_reindex_cost Z _ _ hdec).trans ?_
    calc ∑ p : B × B, specNorm (Matrix.single p.1 p.2 (1 : ℂ)) * specNorm (blk p)
        ≤ ∑ p : B × B, specNorm Z := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          rw [g53i_sn, g53i_sn, g53i_sn, hblk]
          calc _ ≤ 1 * ‖P p.1 * Z * (P p.2)ᴴ‖ :=
                mul_le_mul_of_nonneg_right (g53i_single_le _ _) (norm_nonneg _)
            _ ≤ ‖Z‖ := by rw [one_mul]; exact g53i_compress_le _ _ (hP _) (hP _) Z
      _ = (Fintype.card B : ℝ) ^ 2 * specNorm Z := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]; push_cast; ring
  have hEside : projectiveNorm Z ≤ (Fintype.card E : ℝ) ^ 2 * specNorm Z := by
    let P : E → Matrix B (B × E) ℂ := fun f => Matrix.of fun c x => if x = (c, f) then 1 else 0
    have hP : ∀ f, P f * (P f)ᴴ = 1 := by
      intro f; ext e e'
      simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      split_ifs <;> simp_all
    let blk : E × E → Matrix B B ℂ := fun p => Matrix.of fun c c' => Z (c, p.1) (c', p.2)
    have hblk : ∀ p, blk p = P p.1 * Z * (P p.2)ᴴ := by
      intro p; ext e e'
      simp [blk, P, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hdec : Z = ∑ p : E × E, Matrix.kronecker (blk p) (Matrix.single p.1 p.2 (1 : ℂ)) := by
      ext x y
      simp [blk, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
        Fintype.sum_prod_type]
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun b _ hb => Finset.sum_eq_zero
          (fun c _ => if_neg (fun h => hb h.1))),
        Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun c _ hc => if_neg (fun h => hc h.2))]
      simp
    refine (g53i_reindex_cost Z _ _ hdec).trans ?_
    calc ∑ p : E × E, specNorm (blk p) * specNorm (Matrix.single p.1 p.2 (1 : ℂ))
        ≤ ∑ p : E × E, specNorm Z := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          rw [g53i_sn, g53i_sn, g53i_sn, hblk]
          calc _ ≤ ‖P p.1 * Z * (P p.2)ᴴ‖ * 1 :=
                mul_le_mul_of_nonneg_left (g53i_single_le _ _) (norm_nonneg _)
            _ ≤ ‖Z‖ := by rw [mul_one]; exact g53i_compress_le _ _ (hP _) (hP _) Z
      _ = (Fintype.card E : ℝ) ^ 2 * specNorm Z := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]; push_cast; ring
  rcases le_total ((Fintype.card B : ℝ) ^ 2) ((Fintype.card E : ℝ) ^ 2) with h | h
  · rw [min_eq_left h]; exact hBside
  · rw [min_eq_right h]; exact hEside

end
