-- Prove2me | solution 1 for WagerFairDiv.theorem_3_bbOnSupport_of_pareto
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:31:01.305681+00:00
-- url     : https://prove2.me/submissions/d4e4badd-b313-4263-b3f2-a47cd159d76b

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hA : WagerFairDiv.IsAllocMech A)
    (hAB : WagerFairDiv.Corresponding A B) (hPO : WagerFairDiv.ParetoOptimal A) :
    WagerFairDiv.BBOnSupport B := by
  intro p w j hj
  obtain ⟨i0, hi0⟩ := hj
  have hA1 : ∑ i, A p w i j = 1 := by
    by_contra hne
    have hlt : ∑ i, A p w i j < 1 := lt_of_le_of_ne ((hA p w).2 j) hne
    obtain ⟨s, hs⟩ : ∃ s, s = 1 - ∑ i, A p w i j := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; linarith
    let a' : Fin n → Fin m → ℝ := fun i k => A p w i k + if i = i0 ∧ k = j then s else 0
    have hite : ∀ i k, 0 ≤ (if i = i0 ∧ k = j then s else 0) := by
      intro i k; split_ifs <;> linarith
    have feas : WagerFairDiv.IsFeasibleAlloc a' := by
      refine ⟨fun i k => add_nonneg ((hA p w).1 i k) (hite i k), fun k => ?_⟩
      simp only [a']
      rw [Finset.sum_add_distrib]
      by_cases hk : k = j
      · subst hk
        simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linarith
      · simp only [hk, and_false, if_false, Finset.sum_const_zero, add_zero]
        exact (hA p w).2 k
    have hv : ∀ i, WagerFairDiv.val (p i).1 (A p w i) ≤ WagerFairDiv.val (p i).1 (a' i) := by
      intro i
      unfold WagerFairDiv.val
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (hite i k)) ((p i).2.1 k))
    have hstrict : WagerFairDiv.val (p i0).1 (A p w i0) < WagerFairDiv.val (p i0).1 (a' i0) := by
      unfold WagerFairDiv.val
      have e : ∑ k, (p i0).1 k * a' i0 k = ∑ k, (p i0).1 k * A p w i0 k + (p i0).1 j * s := by
        simp only [a', mul_add, Finset.sum_add_distrib, true_and, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e]
      have := mul_pos hi0 hs0
      linarith
    obtain ⟨k, hk⟩ := hPO p w a' feas ⟨i0, hstrict⟩
    linarith [hv k]
  rw [Finset.sum_congr rfl (fun i _ => hAB p w i j), ← Finset.mul_sum, hA1, mul_one]
