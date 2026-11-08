-- Prove2me | solution 1 for ParallelLotteries.cost_le_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:36:28.354764+00:00
-- url     : https://prove2.me/submissions/de0ad6be-48ce-4d06-a32a-a9082470b056

import Mathlib
import Definitions.Def_ParallelLotteries_Model
import Definitions.Def_ParallelLotteries_Budget

open ParallelLotteries in
theorem solution {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : ParallelLotteries.Strategy n k) :
    (∀ i, ParallelLotteries.chi s p i ≤ (s.tickets i : ℝ) * p i) ∧
      ParallelLotteries.cost k p (ParallelLotteries.chi s p) ≤ 1 := by
  have hchi : ∀ i, ParallelLotteries.chi s p i ≤ (s.tickets i : ℝ) * p i := by
    intro i
    unfold ParallelLotteries.chi
    have hp1 := hp i
    have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ -p i by linarith) (s.tickets i)
    rw [mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg] at hB
    have hA0 : 0 ≤ 1 - (1 - p i) ^ s.tickets i :=
      sub_nonneg.2 (pow_le_one₀ (by linarith) (by linarith))
    refine (mul_le_mul_of_nonneg_left (Finset.prod_le_one
      (fun j _ => pow_nonneg (by linarith [(hp j).2]) _)
      (fun j _ => pow_le_one₀ (by linarith [(hp j).2]) (by linarith [(hp j).1]))) hA0).trans ?_
    linarith
  refine ⟨hchi, ?_⟩
  unfold ParallelLotteries.cost
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), ParallelLotteries.chi s p i / p i ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), (s.tickets i : ℝ) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [div_le_iff₀ hi.2]
    exact hchi i
  have hsub : ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), (s.tickets i : ℝ) ≤
      ∑ i, (s.tickets i : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Nat.cast_nonneg _)
  have htot : ∑ i, (s.tickets i : ℝ) ≤ k := by
    have h := (show ∑ i, ((s.1.1 i : Fin (k + 1)) : ℕ) ≤ k from s.2)
    unfold ParallelLotteries.Strategy.tickets
    exact_mod_cast h
  rw [one_div, inv_mul_le_iff₀ hk']
  linarith
