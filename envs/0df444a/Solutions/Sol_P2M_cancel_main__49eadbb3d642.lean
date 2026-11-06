-- Prove2me | solution 1 for P2M_cancel_main__49eadbb3d642
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:36:17.09594+00:00
-- url     : https://prove2.me/submissions/a68bfa6c-5792-410b-ba20-81f37649c0db

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open Real BigOperators

private theorem sum_range_succ_local (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have h := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at h
  rw [Finset.sum_range_succ, h]
  ring

theorem solution {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  have l1 (i : ℕ) :
      (g i - g (i + 1)) * ∑ j ∈ Finset.range (i + 1), f j ≤
        (g i - g (i + 1)) * (C * (i + 1)) := by
    apply mul_le_mul le_rfl (by simpa only [cumsum, Nat.cast_add, Nat.cast_one] using hf' (i + 1))
      (Finset.sum_nonneg (fun j _ => hf j)) ?_
    simp only [sub_nonneg]
    apply hg'
    simp
  have l2 (i : ℕ) : C * (↑(i + 1) + 1) - C * (↑i + 1) = C := by simp; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg (fun i _ => hf i)
  change (∑ i ∈ Finset.range n, f i * g i) ≤ C * cumsum g n
  calc
    ∑ i ∈ Finset.range n, f i * g i =
        g (n - 1) * cumsum f n +
          ∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * cumsum f (i + 1) := by
      convert_to ∑ i ∈ Finset.range n, (g i) • (f i) = _
      · simp [mul_comm]
      rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      simp_rw [← neg_smul, neg_sub, smul_eq_mul]
      rfl
    _ ≤ g (n - 1) * (C * n) +
          ∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (i + 1)) := by
      apply _root_.add_le_add
      · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
      · exact Finset.sum_le_sum (fun i _ => l1 i)
    _ = C * cumsum g n := by
      have hsum :
          (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (i + 1))) =
            ∑ i ∈ Finset.range (n - 1), (C * (i + 1)) • (g i - g (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [mul_comm]
      rw [hsum, Finset.sum_range_by_parts]
      simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ_local]
      unfold cumsum
      cases n with
      | zero => simp
      | succ n =>
        cases n <;>
          simp [Nat.cast_add, Nat.cast_one, Finset.sum_range_succ] <;>
          ring
