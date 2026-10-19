-- Prove2me | solution 1 for SeqLoss.Equidistance.sq_dist_ideal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:44:58.912065+00:00
-- url     : https://prove2.me/submissions/e0337853-49b7-4be5-b6a6-11d45dd26357

import Definitions.Def_SeqLoss_Equidistance_IdealAllocations
open SeqLoss.Equidistance
open scoped BigOperators

private lemma pref_card {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  classical
  calc
    _ = (Finset.range k).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        simpa using hi
      · intro i hi j hj hij
        exact Fin.ext hij
      · intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        exact ⟨⟨j, lt_of_lt_of_le hjk hk⟩, by simp [hjk], rfl⟩
    _ = k := Finset.card_range k

private lemma pref_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1), x j) =
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), x j) + x i := by
  classical
  have heq : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hji : j = i
      · exact Or.inl hji
      · right
        have : j.val ≠ i.val := fun he => hji (Fin.ext he)
        omega
    · rintro (rfl | h) <;> omega
  rw [heq, Finset.sum_insert (by simp)]
  ring

private lemma sqdist {n : ℕ} (ℓ x : Fin n → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    euclDist x (ideal ℓ k) ^ 2 =
      (∑ i, x i ^ 2)
        - 2 * SeqLoss.FixedFraction.total ℓ / (k : ℝ) * (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i)
        + SeqLoss.FixedFraction.total ℓ ^ 2 / (k : ℝ) := by
  classical
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold euclDist
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Real.dist_eq, sq_abs]
  have hexp : ∀ i : Fin n, (x i - ideal ℓ k i) ^ 2 =
      x i ^ 2 + (if i.val < k then
        -(2 * SeqLoss.FixedFraction.total ℓ / (k : ℝ) * x i) + (SeqLoss.FixedFraction.total ℓ / k)^2 else 0) := by
    intro i
    unfold ideal
    split_ifs <;> ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, pref_card hkn]
  field_simp
  <;> ring

theorem solution {n : ℕ} (ℓ x : Fin n → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    euclDist x (ideal ℓ k) ^ 2 =
      (∑ i, x i ^ 2)
        - 2 * SeqLoss.FixedFraction.total ℓ / (k : ℝ) * (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i)
        + SeqLoss.FixedFraction.total ℓ ^ 2 / (k : ℝ) := by
  exact sqdist ℓ x k hk1 hkn
