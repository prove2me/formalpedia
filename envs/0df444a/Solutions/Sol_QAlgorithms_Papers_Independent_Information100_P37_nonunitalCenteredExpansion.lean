-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.nonunitalCenteredExpansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:06.322991+00:00
-- url     : https://prove2.me/submissions/a6157c6b-6674-4fb2-b720-e0a90c83ea24

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7D_frob_sq {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    frobNorm X ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [Complex.sq_norm]

lemma X7D_normSq_re (z : ℂ) : Complex.normSq z = (conj z * z).re := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma X7D_kraus_lin {ι K α : Type*} [Fintype ι] [Fintype K] [Fintype α]
    (A : K → Matrix ι ι ℂ) (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    krausApply A (∑ a, f a • X a) = ∑ a, f a • krausApply A (X a) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma X7D_diag_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℂ) :
    Matrix.diagonal p = ∑ i, p i • Matrix.single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : a = b
  · subst h; simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    aesop

lemma X7D_offDiag_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    offDiagonal (∑ a, f a • X a) = ∑ a, f a • offDiagonal (X a) := by
  ext l m
  simp only [offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

lemma X7D_E_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (q : ι → ℂ) :
    offDiagonal (E (Matrix.diagonal q)) = ∑ i, q i • channelOutput E i := by
  obtain ⟨m, A, -, hA⟩ := hE
  rw [hA, X7D_diag_eq, X7D_kraus_lin, X7D_offDiag_sum]
  simp [channelOutput, hA]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : Superop ι ι) (hE : IsChannel E) :
    channelOffset E = offDiagonal (E ((1 / (Fintype.card ι : ℂ)) • (1 : Matrix ι ι ℂ))) ∧
    (∀ p, IsPopulation p →
      offDiagonal (E (inputDensity p)) = channelOffset E + ∑ i, (centered p i : ℂ) • channelOutput E i ∧
      generated E p = frobNorm (channelOffset E) ^ 2 +
        2 * (∑ i, centered p i * (((channelOffset E)ᴴ * channelOutput E i).trace).re) +
        ∑ i, ∑ j, centered p i * centered p j * (((channelOutput E i)ᴴ * channelOutput E j).trace).re) := by
  have h1 : channelOffset E = offDiagonal (E ((1 / (Fintype.card ι : ℂ)) • (1 : Matrix ι ι ℂ))) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, X7D_E_diag E hE, channelOffset,
      Finset.smul_sum]
    simp
  have h2 : ∀ p : ι → ℝ, offDiagonal (E (inputDensity p)) =
      channelOffset E + ∑ i, (centered p i : ℂ) • channelOutput E i := by
    intro p
    rw [inputDensity, X7D_E_diag E hE, channelOffset, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    simp [centered]
  refine ⟨h1, fun p _ => ⟨h2 p, ?_⟩⟩
  set C := channelOffset E
  set O := channelOutput E
  have hcoh : generated E p = ∑ l, ∑ m, Complex.normSq
      (offDiagonal (E (inputDensity p)) l m) := by
    simp only [generated, coherence, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply,
      Matrix.diag]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  rw [hcoh, h2 p, X7D_frob_sq]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.normSq_add, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.re_sum]
  have hS : ∀ l m, Complex.normSq (∑ i, (centered p i : ℂ) * O i l m) =
      ∑ i, ∑ j, centered p i * centered p j * (conj (O i l m) * O j l m).re := by
    intro l m
    rw [X7D_normSq_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    rw [show (centered p i : ℂ) * conj (O i l m) * ((centered p j : ℂ) * O j l m) =
      ((centered p i * centered p j : ℝ) : ℂ) * (conj (O i l m) * O j l m) by push_cast; ring, Complex.re_ofReal_mul]
  have hX : ∀ l m, (C l m * conj (∑ i, (centered p i : ℂ) * O i l m)).re =
      ∑ i, centered p i * (conj (C l m) * O i l m).re := by
    intro l m
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show conj (C l m) * ((centered p i : ℂ) * O i l m) = (centered p i : ℂ) * (conj (C l m) * O i l m) by ring,
      Complex.re_ofReal_mul]
  simp only [hS, hX, Finset.mul_sum, Finset.sum_add_distrib]
  rw [add_right_comm]
  congr 1
  congr 1
  · have e2 : ∀ l : ι, (∑ m, ∑ i, 2 * (centered p i * (conj (C l m) * O i l m).re))
        = ∑ i, ∑ m, 2 * (centered p i * (conj (C l m) * O i l m).re) := fun l => Finset.sum_comm
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · have e1 : ∀ l : ι, (∑ m, ∑ i, ∑ j, centered p i * centered p j * (conj (O i l m) * O j l m).re)
        = ∑ i, ∑ j, ∑ m, centered p i * centered p j * (conj (O i l m) * O j l m).re := by
      intro l
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
