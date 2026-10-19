-- Prove2me | solution 1 for QuantumParallelRepetition.arbitrarily_large_witness_of_not_hasExponentialBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/2153103c-b45e-4580-a606-df8f3e06cebf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_not_hasExponentialBound_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
namespace QuantumParallelRepetition
theorem _root_.solution
    {v : ℕ → ℝ}
    (hv : ∀ n : ℕ, v n ≤ 1)
    (h_no_bound : ¬ HasExponentialBound v)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Real.exp (-c * (n : ℝ)) < v n := by
  have h_witness := (not_hasExponentialBound_iff v).mp h_no_bound
  obtain ⟨n, hn⟩ :=
    h_witness c hc (Real.exp (c * (N : ℝ))) (Real.exp_pos _)
  have hN : N < n := by
    by_contra h_not
    have hnN : n ≤ N := Nat.le_of_not_gt h_not
    have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have h_nonneg : 0 ≤ c * ((N : ℝ) - (n : ℝ)) :=
      mul_nonneg hc.le (sub_nonneg.mpr hnN_real)
    have h_lower :
        1 ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
      calc
        1 ≤ Real.exp (c * ((N : ℝ) - (n : ℝ))) :=
          Real.one_le_exp h_nonneg
        _ = Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    linarith [hv n]
  refine ⟨n, hN, ?_⟩
  have h_prefactor : 1 ≤ Real.exp (c * (N : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc.le (Nat.cast_nonneg _))
  calc
    Real.exp (-c * (n : ℝ)) =
        1 * Real.exp (-c * (n : ℝ)) := by rw [one_mul]
    _ ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h_prefactor (Real.exp_pos _).le
    _ < v n := hn
end QuantumParallelRepetition
