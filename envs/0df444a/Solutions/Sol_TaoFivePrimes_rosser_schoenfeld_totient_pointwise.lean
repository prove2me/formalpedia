-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_pointwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T08:42:45.755882+00:00
-- url     : https://prove2.me/submissions/ad290105-ad31-44fb-b6cd-158fa0964a07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_small
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_large

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_totient_pointwise`

The target is the uniform form of Rosser–Schoenfeld (1962), Theorem 15,
used by Tao in the proof of Proposition 4.10 (arXiv:1201.6656): for every
`n ≥ 3`,

`n/φ(n) < e^γ log log n + 2.50637/log log n`.

The reduction follows the two halves of the proof in §9 of the source:

* finite range `3 ≤ n < e^294`: `TaoFivePrimes.rosser_schoenfeld_totient_small`
  (Lemma 14 with the Rosser–Walker tabulation, covering `n < exp θ(313)` and
  hence `n < e^294` because `294 < θ(313)`);
* analytic range `e^294 ≤ n`: `TaoFivePrimes.rosser_schoenfeld_totient_large`
  (Lemma 15, from Theorem 33, the Mertens product estimate (3.29) and the
  Chebyshev bounds for `θ`, valid for `log n ≥ 294`).

The wrapper is the resulting case split at `n = e^294`.
-/

namespace TaoFivePrimes

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  by_cases hfin : (n : ℝ) < Real.exp 294
  · exact rosser_schoenfeld_totient_small n hn hfin
  · exact rosser_schoenfeld_totient_large n hn (not_lt.mp hfin)

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) :=
  TaoFivePrimes.solution n hn

#print axioms solution
