-- Prove2me | solution 1 for SelfDualLP.Complexity.theorem_6_data
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:21:32.441983+00:00
-- url     : https://prove2.me/submissions/72aa78b1-fa62-477a-b80a-46fafc580e7c

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_BitLength

open Matrix


namespace SelfDualLP.Complexity

section BitData

lemma size_add_le' (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 1 ≤ 2 ^ Nat.size a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ Nat.size b := Nat.one_le_two_pow
  rw [pow_add]; nlinarith

lemma size_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    Nat.size (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Nat.size (f i) :=
  Finset.le_sum_of_subadditive Nat.size Nat.size_zero.le size_add_le' s f

lemma natAbs_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs :=
  Finset.le_sum_of_subadditive Int.natAbs Int.natAbs_zero.le Int.natAbs_add_le s f

lemma size_le_self' (k : ℕ) : Nat.size k ≤ k := Nat.size_le.2 Nat.lt_two_pow_self

lemma size_le_intSize (v : ℤ) : Nat.size v.natAbs ≤ intSize v := by unfold intSize; omega

lemma intSize_bbar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (i : Fin m) :
    intSize (bbarInt A b i) ≤ intSize (b i) + ∑ j, intSize (A i j) := by
  have e : bbarInt A b i = b i - ∑ j, A i j := by
    simp [bbarInt, mulVec, dotProduct]
  have h1 : (bbarInt A b i).natAbs ≤ (b i).natAbs + ∑ j, (A i j).natAbs := by
    rw [e]
    exact le_trans (Int.natAbs_sub_le _ _) (add_le_add le_rfl (natAbs_sum_le' _ _))
  have h2 := le_trans (Nat.size_le_size h1) (size_add_le' _ _)
  have h3 : Nat.size (∑ j, (A i j).natAbs) ≤ ∑ j, Nat.size (A i j).natAbs := size_sum_le' _ _
  have h4 : ∑ j, Nat.size (A i j).natAbs ≤ ∑ j, intSize (A i j) :=
    Finset.sum_le_sum (fun j _ => size_le_intSize _)
  unfold intSize at *
  omega

lemma intSize_cbar {n : ℕ} (c : Fin n → ℤ) (j : Fin n) :
    intSize (cbarInt c j) ≤ intSize (c j) + 1 := by
  have e : cbarInt c j = c j - 1 := by simp [cbarInt]
  have h1 : (cbarInt c j).natAbs ≤ (c j).natAbs + 1 := by
    rw [e]; exact le_trans (Int.natAbs_sub_le _ _) (by simp)
  have h2 := le_trans (Nat.size_le_size h1) (size_add_le' _ _)
  have : Nat.size 1 = 1 := Nat.size_one
  unfold intSize; omega

lemma hlpBit_le {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (c : Fin n → ℤ) : hlpBitLength A b c ≤ 10 * bitLength A b c := by
  have hB : vecSize (bbarInt A b) ≤ vecSize b + ∑ i, ∑ j, intSize (A i j) := by
    unfold vecSize
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => intSize_bbar A b i)
    rw [Finset.sum_add_distrib] at this
    omega
  have hC : vecSize (cbarInt c) ≤ 2 * vecSize c := by
    unfold vecSize
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => intSize_cbar c j)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at this
    omega
  have hZ : intSize (zbarInt c) ≤ vecSize c + 2 := by
    have h1 : (zbarInt c).natAbs ≤ (∑ j, (c j).natAbs) + 1 := by
      unfold zbarInt
      exact le_trans (Int.natAbs_add_le _ _) (by simpa using natAbs_sum_le' Finset.univ c)
    have h2 := le_trans (Nat.size_le_size h1) (size_add_le' _ _)
    have h3 : Nat.size (∑ j, (c j).natAbs) ≤ ∑ j, Nat.size (c j).natAbs := size_sum_le' _ _
    have h4 : ∑ j, Nat.size (c j).natAbs ≤ ∑ j, intSize (c j) :=
      Finset.sum_le_sum (fun j _ => size_le_intSize _)
    have : Nat.size 1 = 1 := Nat.size_one
    have e1 : vecSize c = n + ∑ j, intSize (c j) := rfl
    show 1 + Nat.size (zbarInt c).natAbs ≤ vecSize c + 2
    omega
  have hN : intSize (-((n : ℤ) + 1)) ≤ n + 2 := by
    unfold intSize
    have e : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [e]; have := size_le_self' (n + 1); omega
  have hcn : n ≤ vecSize c := by unfold vecSize; omega
  have hb0 : vecSize b ≤ bitLength A b c := by unfold bitLength; omega
  unfold hlpBitLength
  unfold bitLength at *
  unfold matSize at *
  omega

theorem t6data_core :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
      bbar (castMat A) (castVec b) (ones n) = castVec (bbarInt A b) ∧
      cbar (castMat A) (castVec c) 0 (ones n) = castVec (cbarInt c) ∧
      zbar (castVec b) (castVec c) (ones n) 0 = ((zbarInt c : ℤ) : ℝ) ∧
      (hlpBitLength A b c : ℝ) ≤ C * (bitLength A b c : ℝ) := by
  refine ⟨10, by norm_num, fun m n hn A b c => ⟨?_, ?_, ?_, ?_⟩⟩
  · funext i
    simp [bbar, bbarInt, castVec, castMat, mulVec, dotProduct, ones]
  · funext j
    simp [cbar, cbarInt, castVec, ones]
  · simp [zbar, zbarInt, castVec, ones, dotProduct]
  · exact_mod_cast hlpBit_le hn A b c

end BitData
end SelfDualLP.Complexity

open SelfDualLP.Complexity


theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ), 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ),
      bbar (castMat A) (castVec b) (ones n) = castVec (bbarInt A b) ∧
      cbar (castMat A) (castVec c) 0 (ones n) = castVec (cbarInt c) ∧
      zbar (castVec b) (castVec c) (ones n) 0 = ((zbarInt c : ℤ) : ℝ) ∧
      (hlpBitLength A b c : ℝ) ≤ C * (bitLength A b c : ℝ) := by
  exact t6data_core
