-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_small
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T08:49:12.698074+00:00
-- url     : https://prove2.me/submissions/5db6409d-0d69-464c-ad24-3c0bc9bb40f7

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma14
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_finite_verification

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_totient_small`

The target is the finite half (`3 ≤ n < e^294`) of Rosser–Schoenfeld (1962),
Theorem 15: for `3 ≤ n < e^294`,

`n/φ(n) < e^γ log log n + 2.50637/log log n`.

The reduction follows §9 of the source (pp. 88–89), splitting the proof into:

* `TaoFivePrimes.rosser_schoenfeld_totient_finite_verification`: the
  Rosser–Walker numerical verification — for each `3 ≤ n < e^294` there is an
  `m` with `n < exp θ(p_{m+1})` and
  `∏_{i≤m} p_i/(p_i-1) < e^γ log log n + 2.50637/log log n` (checked at the
  left endpoint of the interval `[e^{θ(p_m)}, e^{θ(p_{m+1})})` containing `n`,
  via monotonicity of `log log n`, with the exceptional case
  `n = 223092870` covered by the sharpened constant);
* `TaoFivePrimes.rosser_schoenfeld_totient_lemma14`: the elementary primorial
  bound `n/φ(n) ≤ ∏_{i≤m} p_i/(p_i-1)` under `n < exp θ(p_{m+1})`.

The wrapper combines the two: extract `m` from the verification and apply
Lemma 14.
-/

namespace TaoFivePrimes

theorem solution (n : ℕ) (hn : 3 ≤ n) (hfin : (n : ℝ) < Real.exp 294) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  obtain ⟨m, hm, hθ, hnum⟩ :=
    rosser_schoenfeld_totient_finite_verification n hn hfin
  exact lt_of_le_of_lt (rosser_schoenfeld_totient_lemma14 n m (by omega) hm hθ) hnum

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) (hfin : (n : ℝ) < Real.exp 294) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) :=
  TaoFivePrimes.solution n hn hfin

#print axioms solution
