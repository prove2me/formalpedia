-- Prove2me | solution 1 for binomial_tail_reflect
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:35:02.020009+00:00
-- url     : https://prove2.me/submissions/2e571d71-d687-4049-a65a-cb336032400c

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open scoped BigOperators
open Finset

/-- **Binomial upper-tail reflection (k ↔ N-k).**  For `m ≤ N` and any `q`,
`∑_{k=N-m}^{N} C(N,k) q^k (1-q)^{N-k} = ∑_{j=0}^{m} C(N,j) (1-q)^j q^{N-j}`.
Substituting `j = N-k` turns the high tail of `Bin(N,q)` into the low tail of `Bin(N,1-q)`. -/
theorem solution (N m : ℕ) (hm : m ≤ N) (q : ℝ) :
    (∑ k ∈ Finset.Ico (N-m) (N+1),
        (Nat.choose N k : ℝ) * q ^ k * (1 - q) ^ (N - k))
      = ∑ j ∈ Finset.range (m+1),
        (Nat.choose N j : ℝ) * (1 - q) ^ j * q ^ (N - j) := by
  -- reindex k = N - j over j ∈ range (m+1); image is Ico (N-m) (N+1)
  rw [← Finset.sum_range_reflect (fun j =>
        (Nat.choose N j : ℝ) * (1 - q) ^ j * q ^ (N - j)) (m+1)]
  -- now LHS sum over Ico (N-m) (N+1), RHS sum over range (m+1) with j ↦ (m+1-1-j)=m-j
  apply Finset.sum_nbij' (fun k => k - (N - m)) (fun j => j + (N - m))
  · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
  · intro k hk; rw [Finset.mem_Ico] at hk; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have hidx : m + 1 - 1 - (k - (N - m)) = N - k := by omega
    rw [hidx]
    have hcho : Nat.choose N (N - k) = Nat.choose N k := Nat.choose_symm (by omega)
    rw [hcho]
    have hNNk : N - (N - k) = k := by omega
    rw [hNNk]
    ring
