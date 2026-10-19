-- Prove2me | solution 1 for SeqLoss.Equidistance.prefix_system_solution
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:45:15.068998+00:00
-- url     : https://prove2.me/submissions/bea45ad2-3b92-449c-848e-9eaa6d84ba9c

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

theorem solution {n : ℕ} (hn : 0 < n) (ℓ x : Fin n → ℝ) (α : ℝ)
    (hsum : ∑ i, x i = SeqLoss.FixedFraction.total ℓ)
    (hsys : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i) - SeqLoss.FixedFraction.total ℓ / 2 = α * (k : ℝ)) :
    α = SeqLoss.FixedFraction.total ℓ / (2 * (n : ℝ)) ∧
      ((∀ i j, ℓ i = ℓ j) → x = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hall : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp [i.isLt]
  have htotal := hsys n hn (le_refl n)
  rw [hall, hsum] at htotal
  have hα : α = SeqLoss.FixedFraction.total ℓ / (2 * (n : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hnR)).mpr
    linarith
  refine ⟨hα, ?_⟩
  intro heq
  funext i
  have hconst : SeqLoss.FixedFraction.total ℓ = (n : ℝ) * ℓ i := by
    unfold SeqLoss.FixedFraction.total
    calc
      _ = ∑ j : Fin n, ℓ i := Finset.sum_congr rfl (fun j _ => heq j i)
      _ = (n : ℝ) * ℓ i := by simp
  have hαi : α = (1 / 2 : ℝ) * ℓ i := by
    rw [hα, hconst]
    field_simp
    <;> ring
  have hsuc := hsys (i.val + 1) (by omega) (by omega)
  have hdiff := pref_succ x i
  unfold SeqLoss.FixedFraction.fixedFraction
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    simp only [hi, zero_add, Nat.cast_one, mul_one] at hsuc
    simp only [hi, zero_add, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty, zero_add] at hdiff
    rw [hdiff] at hsuc
    change x i = (1 / 2 : ℝ) * ℓ i + (1 - 1 / 2) * SeqLoss.FixedFraction.total ℓ
    linarith
  · rw [if_neg hi, add_zero]
    have hprev := hsys i.val (by omega) (by omega)
    push_cast at hsuc
    linarith