-- Prove2me | solution 1 for WilliamsonShmoys.shifting_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-30T13:52:51.94498+00:00
-- url     : https://prove2.me/submissions/fb6b1fe7-712c-41a4-8c2f-8018ad72f73e

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

theorem solution {V : Type} (G : SimpleGraph V) (w : V → ℝ) (c : V → ℕ)
    (k : ℕ) (hk : 0 < k) (A : Finset V)
    (hA : ∀ j < k, ∀ S : Finset V, G.IsIndepSet (S : Set V) →
      (∀ v ∈ S, c v % k ≠ j) → ∑ i ∈ S, w i ≤ ∑ i ∈ A, w i)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    (1 - 1 / (k : ℝ)) * ∑ i ∈ S, w i ≤ ∑ i ∈ A, w i := by
  classical
  have hsub : ∀ j < k, ∑ i ∈ S.filter (fun v => c v % k ≠ j), w i ≤ ∑ i ∈ A, w i := by
    intro j hj
    refine hA j hj _ (hS.mono (by intro x hx; simp at hx; exact hx.1)) ?_
    intro v hv; simp at hv; exact hv.2
  have hsum : ∑ j ∈ Finset.range k, ∑ i ∈ S.filter (fun v => c v % k ≠ j), w i
      = ((k : ℝ) - 1) * ∑ i ∈ S, w i := by
    rw [Finset.sum_comm' (t' := S)
      (s' := fun i => (Finset.range k).filter (fun j => c i % k ≠ j))]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have : (Finset.range k).filter (fun j => c i % k ≠ j)
          = (Finset.range k).erase (c i % k) := by
        ext j; simp [and_comm, eq_comm]
      rw [this, Finset.card_erase_of_mem (by simp [Nat.mod_lt _ hk])]
      simp [Nat.cast_sub (show 1 ≤ k from hk)]
    · intro j i; simp; tauto
  have hle : ∑ j ∈ Finset.range k, ∑ i ∈ S.filter (fun v => c v % k ≠ j), w i
      ≤ (k : ℝ) * ∑ i ∈ A, w i := by
    calc _ ≤ ∑ j ∈ Finset.range k, ∑ i ∈ A, w i :=
          Finset.sum_le_sum fun j hj => hsub j (Finset.mem_range.1 hj)
      _ = _ := by simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hsum] at hle
  set W := ∑ i ∈ S, w i
  set B := ∑ i ∈ A, w i
  have key : (k : ℝ) * ((1 - 1 / (k : ℝ)) * W) = ((k : ℝ) - 1) * W := by
    field_simp
  exact le_of_mul_le_mul_left (by rw [key]; exact hle) hkpos
