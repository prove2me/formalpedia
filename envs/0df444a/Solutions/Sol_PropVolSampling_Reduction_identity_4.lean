-- Prove2me | solution 1 for PropVolSampling.Reduction.identity_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:57:21.672425+00:00
-- url     : https://prove2.me/submissions/eeb9b094-b572-4ede-b227-c26afcde8c97

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

noncomputable section
open Matrix Finset Polynomial
namespace PropVolSampling.Reduction.SpectralProof

lemma esymm_zero_cons (s : Multiset ℝ) (k : ℕ) : (0 ::ₘ s).esymm k = s.esymm k := by
  cases k with
  | zero => simp [Multiset.esymm]
  | succ k => simp [Multiset.esymm, Multiset.map_map]

lemma esymm_zero_padding (s : Multiset ℝ) (r k : ℕ) :
    (r • ({0} : Multiset ℝ) + s).esymm k = s.esymm k := by
  induction r with
  | zero => simp
  | succ r ih => simpa only [succ_nsmul, Multiset.singleton_add, add_assoc,
      Multiset.add_cons, esymm_zero_cons] using ih

lemma Ek_mul_swap_of_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) (k : ℕ)
    (h : Fintype.card n ≤ Fintype.card m) : Ek k (A*B) = Ek k (B*A) := by
  unfold Ek
  rw [Matrix.charpoly_mul_comm_of_le A B h, Polynomial.roots_mul
    (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, esymm_zero_padding]

lemma Ek_mul_swap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) (k : ℕ) : Ek k (A*B) = Ek k (B*A) := by
  rcases le_total (Fintype.card n) (Fintype.card m) with hn | hm
  · exact Ek_mul_swap_of_le A B k hn
  · exact (Ek_mul_swap_of_le B A k hm).symm

lemma coeff_charpoly {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) (k : ℕ) (hk : k ≤ Fintype.card m) :
    M.charpoly.coeff (Fintype.card m-k) = (-1:ℝ)^k * Ek k M := by
  have h := Polynomial.coeff_eq_esymm_roots_of_splits hM.splits_charpoly
    (show Fintype.card m-k ≤ M.charpoly.natDegree by
      rw [Matrix.charpoly_natDegree_eq_dim]; omega)
  simpa only [Matrix.charpoly_natDegree_eq_dim, (Matrix.charpoly_monic M).leadingCoeff,
    one_mul, Nat.sub_sub_self hk, Ek] using h

lemma Ek_eq_sum_minors {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) (k : ℕ) :
    Ek k M = ∑ S ∈ powersetCard k (univ : Finset m),
      (M.submatrix (Subtype.val : S → m) (Subtype.val : S → m)).det := by
  by_cases hk : k ≤ Fintype.card m
  · apply (mul_left_cancel₀ (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)))
    rw [← coeff_charpoly M hM k hk, Matrix.charpoly_coeff_eq_sum_minors M k hk]
  · have hkc : Fintype.card m < k := by omega
    have hroots : M.charpoly.roots.card < k :=
      lt_of_le_of_lt (by simpa only [Matrix.charpoly_natDegree_eq_dim] using
        Polynomial.card_roots' M.charpoly) hkc
    have he : powersetCard k (univ : Finset m) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa only [Finset.card_univ] using hkc)
    simp [Ek, Multiset.esymm, Multiset.powersetCard_eq_empty _ hroots, he]

lemma Ek_card_eq_det {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) : Ek (Fintype.card m) M = M.det := by
  have h := coeff_charpoly M hM (Fintype.card m) le_rfl
  simp only [Nat.sub_self] at h
  rw [Matrix.det_eq_sign_charpoly_coeff, h, ← mul_assoc, ← mul_pow]
  simp

end PropVolSampling.Reduction.SpectralProof

open PropVolSampling.Reduction PropVolSampling.Reduction.SpectralProof

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) :
    Ek k (V * Vᵀ) = Ek k (Vᵀ * V) ∧
      Ek k (Vᵀ * V) = ∑ S ∈ powersetCard k (univ : Finset (Fin n)),
        ((colSub V S)ᵀ * colSub V S).det := by
  refine ⟨Ek_mul_swap V Vᵀ k, ?_⟩
  have hH : (Vᵀ * V).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self V
  rw [Ek_eq_sum_minors (Vᵀ*V) hH]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
