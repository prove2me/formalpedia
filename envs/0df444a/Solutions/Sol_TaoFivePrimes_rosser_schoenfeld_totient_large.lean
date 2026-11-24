-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T09:18:51.565343+00:00
-- url     : https://prove2.me/submissions/39237cd4-7639-4913-9831-a7dd25cededa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma15_corrected
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_theta_exists_corrected

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_totient_large`

The target is the analytic half (`log n ≥ 294`) of Rosser–Schoenfeld (1962),
Theorem 15: for `n ≥ e^294`,

`n/φ(n) < e^γ log log n + 2.50637/log log n`.

Following §9 of the source (p. 89), the reduction splits the proof into:

* `TaoFivePrimes.rosser_schoenfeld_totient_theta_exists_corrected`: for
  `log n ≥ 294` there is a real `y` with
  `288 ≤ log n + y`, `log n < θ(log n + y)` and
  `0 ≤ y - 2 ≤ 0.9 log n/log log n` (Theorem 19 for `255 ≤ log n ≤ 1340`,
  inequality (3.14) for `log n ≥ 1340`);
* `TaoFivePrimes.rosser_schoenfeld_totient_lemma15_corrected`: with such a
  `y`, `n/φ(n) < e^γ log log n + 5/(2 log log n)` (equation (3.41)) via
  Theorem 33 and the Mertens product estimate (3.29).

The wrapper extracts `y` from the first child, applies the second, and
weakens `5/2 = 2.5` to `2.50637` using `log log n > 0` for `n ≥ 3`.
-/

namespace TaoFivePrimes

theorem solution (n : ℕ) (hn : 3 ≤ n) (hlarge : Real.exp 294 ≤ (n : ℝ)) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  have hlog : (294 : ℝ) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_exp 294]
    exact Real.log_le_log (Real.exp_pos 294) hlarge
  obtain ⟨y, hy1, hy2, hy3, hy4⟩ :=
    rosser_schoenfeld_totient_theta_exists_corrected n hn hlog
  have h15 := rosser_schoenfeld_totient_lemma15_corrected n y (by omega) hy1 hy2 hy3 hy4
  have hL : 0 < Real.log (Real.log (n : ℝ)) := by
    apply Real.log_pos
    have he1 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have h15' : (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.5 / Real.log (Real.log (n : ℝ)) := by
    have h := h15
    rwa [show (5 : ℝ) / (2 * Real.log (Real.log (n : ℝ))) =
        2.5 / Real.log (Real.log (n : ℝ)) by ring_nf] at h
  have hd : (2.5 : ℝ) / Real.log (Real.log (n : ℝ)) ≤
      2.50637 / Real.log (Real.log (n : ℝ)) :=
    div_le_div_of_nonneg_right (by norm_num) hL.le
  linarith

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) (hlarge : Real.exp 294 ≤ (n : ℝ)) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) :=
  TaoFivePrimes.solution n hn hlarge

#print axioms solution
