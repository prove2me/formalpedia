-- Prove2me | solution 1 for TaoFivePrimes.ramare_squarefree_totient_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T08:19:01.518782+00:00
-- url     : https://prove2.me/submissions/28de8ebe-2848-4cb7-b407-0bd1e420fb48

import Theorems.Thm_TaoFivePrimes_ramare_squarefree_totient_sum_le_large
import Theorems.Thm_TaoFivePrimes_ramare_squarefree_totient_sum_le_small

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

/-!
# Reduction of `TaoFivePrimes.ramare_squarefree_totient_sum_le`

The target `∑_{n ≤ N} μ²(n)/φ(n) ≤ log N + 1.4709` (Ramaré 1995,
Lemma 3.5(1)) is split at the threshold of the source proof, `z = 142300`:

* `TaoFivePrimes.ramare_squarefree_totient_sum_le_large` — the analytic
  range `N ≥ 142300`: the asymptotic expansion of `G` (Lemma 3.2, re-run
  with exponent `0.45` in place of `1/3`) gives `G(z) - log z ≤ 1.4708`
  once `z ≥ 142300` (eqs. (3.10)–(3.12));
* `TaoFivePrimes.ramare_squarefree_totient_sum_le_small` — the finite range
  `1 ≤ N ≤ 142300`, handled by the direct verification with maximum
  `G(7) - log 7 ≤ 1.4709` (eq. (3.13)).

The reduction is the case split at `142300`, weakening the analytic
constant from `1.4708` to `1.4709`.
-/

namespace TaoFivePrimes

theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 := by
  by_cases hsmall : N ≤ 142300
  · exact ramare_squarefree_totient_sum_le_small N hN hsmall
  · have hlarge : 142300 ≤ N := by omega
    have h := ramare_squarefree_totient_sum_le_large N hlarge
    linarith

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4709 :=
  TaoFivePrimes.solution N hN

#print axioms solution
