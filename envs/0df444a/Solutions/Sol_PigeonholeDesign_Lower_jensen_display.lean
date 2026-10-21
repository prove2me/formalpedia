-- Prove2me | solution 1 for PigeonholeDesign.Lower.jensen_display
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:37:05.34399+00:00
-- url     : https://prove2.me/submissions/52ef1563-a79e-48c0-a2c4-0af6d0a824a0

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

theorem solution {K : ℕ} (hK : 1 ≤ K) (L : Fin K → ℝ) (hsum : ∑ k, L k = 1) (T : ℕ) :
    Real.sqrt T * Real.sqrt (K * (1 / (K : ℝ)) ^ 2) ≤ Real.sqrt (T * ∑ k, L k ^ 2) ∧
      Real.sqrt T * Real.sqrt (K * (1 / (K : ℝ)) ^ 2) = Real.sqrt (T / K) ∧
      (0 < T → (Real.sqrt (T * ∑ k, L k ^ 2) = Real.sqrt (T / K) ↔ ∀ k, L k = 1 / K)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hTnonneg : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hsumnonneg : 0 ≤ ∑ k, L k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hconstant : (K : ℝ) * (1 / (K : ℝ)) ^ 2 = 1 / K := by
    field_simp
  have hvariance : (∑ k, (L k - 1 / (K : ℝ)) ^ 2) =
      (∑ k, L k ^ 2) - 1 / K := by
    have hpoint (k : Fin K) : (L k - 1 / (K : ℝ)) ^ 2 =
        L k ^ 2 - (2 / (K : ℝ)) * L k + (1 / (K : ℝ)) ^ 2 := by ring
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum,
      hconstant]
    ring
  have hlower : 1 / (K : ℝ) ≤ ∑ k, L k ^ 2 := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun k _ => sq_nonneg (L k - 1 / (K : ℝ)))
    linarith
  have hbase : Real.sqrt T * Real.sqrt (K * (1 / (K : ℝ)) ^ 2) =
      Real.sqrt (T / K) := by
    rw [hconstant, ← Real.sqrt_mul hTnonneg]
    congr 1
    ring
  refine ⟨?_, hbase, ?_⟩
  · rw [hbase]
    apply Real.sqrt_le_sqrt
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hlower hTnonneg
  · intro hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    constructor
    · intro heq
      have hargs := congrArg (fun x : ℝ => x ^ 2) heq
      rw [Real.sq_sqrt (mul_nonneg hTnonneg hsumnonneg),
        Real.sq_sqrt (div_nonneg hTnonneg (le_of_lt hKpos))] at hargs
      have hsum_eq : ∑ k, L k ^ 2 = 1 / (K : ℝ) := by
        apply (mul_left_cancel₀ (ne_of_gt hTpos))
        simpa only [div_eq_mul_inv, one_mul] using hargs
      have hzero : (∑ k, (L k - 1 / (K : ℝ)) ^ 2) = 0 := by
        rw [hvariance, hsum_eq, sub_self]
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin K))) => sq_nonneg (L k - 1 / (K : ℝ)))).mp hzero
      intro k
      have hk := hall k (Finset.mem_univ k)
      nlinarith [sq_nonneg (L k - 1 / (K : ℝ))]
    · intro hall
      have hsum_eq : (∑ k, L k ^ 2) = 1 / (K : ℝ) := by
        simp_rw [hall]
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] using hconstant
      rw [hsum_eq]
      congr 1
      ring

#print axioms solution
