-- Prove2me | solution 1 for SparseHistComm.eq_8_covering_distortion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:17:10.509218+00:00
-- url     : https://prove2.me/submissions/3aaf6a46-1130-43da-8f72-c5c08cd49ec3

import Mathlib
import Definitions.Def_SparseHistComm_Admissible
import Definitions.Def_SparseHistComm_ind
import Definitions.Def_SparseHistComm_empHist
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_threshold

open SparseHistComm in
theorem solution (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k)
    (x : Fin n → Finset (Fin d)) (hx : Admissible k x) (J : Fin n → ℕ) (hJ : ∀ i, J i ≤ k)
    (y : Fin n → Finset (Fin d)) (hyx : ∀ i, y i ⊆ x i)
    (hycard : ∀ i, (y i).card = min (J i) (x i).card) :
    l1 (empHist y) (empHist x) = ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| ∧
    ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| =
      (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) ∧
    (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) ≤ (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) ∧
    (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) = k - (1 / (n : ℝ)) * ∑ i, (J i : ℝ) ∧
    (threshold n k D ≤ ∑ i, (J i : ℤ) → l1 (empHist y) (empHist x) ≤ D) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hind : ∀ i a, 0 ≤ ind (x i) a - ind (y i) a := by
    intro i a
    by_cases h1 : a ∈ x i
    · by_cases h2 : a ∈ y i
      · simp [ind, h1, h2]
      · simp [ind, h1, h2]
    · by_cases h2 : a ∈ y i
      · exact absurd (hyx i h2) h1
      · simp [ind, h1, h2]
  have hcs : ∀ s : Finset (Fin d), ∑ a, ind s a = (s.card : ℝ) := by
    intro s
    simp [ind]
  have hl1 : ∀ i, l1 (ind (x i)) (ind (y i)) = ((x i).card : ℝ) - (y i).card := by
    intro i
    unfold l1
    rw [Finset.sum_congr rfl (fun a _ => abs_of_nonneg (hind i a)), Finset.sum_sub_distrib,
      hcs, hcs]
  have p1 : l1 (empHist y) (empHist x) =
      ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| := by
    simp only [l1, empHist]
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_sub_comm, ← mul_sub, ← Finset.sum_sub_distrib]
  have p2 : ∑ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| =
      (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) := by
    have hab : ∀ a, |(1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a)| =
        (1 / (n : ℝ)) * ∑ i, (ind (x i) a - ind (y i) a) := fun a =>
      abs_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hind i a)))
    rw [Finset.sum_congr rfl (fun a _ => hab a), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [l1]
    exact Finset.sum_congr rfl (fun a _ => (abs_of_nonneg (hind i a)).symm)
  have p3 : (1 / (n : ℝ)) * ∑ i, l1 (ind (x i)) (ind (y i)) ≤
      (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    rw [hl1, hycard i, Nat.cast_min]
    have hxk : ((x i).card : ℝ) ≤ k := by exact_mod_cast hx i
    have hJk : (J i : ℝ) ≤ k := by exact_mod_cast hJ i
    rcases le_total (J i : ℝ) ((x i).card : ℝ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have p4 : (1 / (n : ℝ)) * ∑ i, ((k : ℝ) - J i) = k - (1 / (n : ℝ)) * ∑ i, (J i : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, ← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  refine ⟨p1, p2, p3, p4, ?_⟩
  intro h
  have h' : (n : ℝ) * k - (⌊(n : ℝ) * D⌋ : ℝ) ≤ ∑ i, (J i : ℝ) := by
    unfold threshold at h
    exact_mod_cast h
  have hfl : (⌊(n : ℝ) * D⌋ : ℝ) ≤ n * D := Int.floor_le _
  have e : (n : ℝ) * ((k : ℝ) - (1 / (n : ℝ)) * ∑ i, (J i : ℝ)) = n * k - ∑ i, (J i : ℝ) := by
    rw [mul_sub, ← mul_assoc, mul_one_div_cancel hn'.ne', one_mul]
  have h5 : (n : ℝ) * ((k : ℝ) - (1 / (n : ℝ)) * ∑ i, (J i : ℝ)) ≤ n * D := by
    rw [e]; linarith
  have h6 := le_of_mul_le_mul_left h5 hn'
  linarith
