-- Prove2me | solution 2 for TaoFivePrimes.rosser_schoenfeld_totient_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T04:41:50.548981+00:00
-- url     : https://prove2.me/submissions/1b6c0ede-0e88-4cb1-865e-163c8919de75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_theta_exists_corrected
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma15_corrected

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) (hlarge : Real.exp 294 ≤ (n : ℝ)) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlogn : (294 : ℝ) ≤ Real.log (n : ℝ) := (Real.le_log_iff_exp_le hn0).2 hlarge
  have hL : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos (by linarith)
  obtain ⟨y, h1, h2, h3, h4⟩ :=
    TaoFivePrimes.rosser_schoenfeld_totient_theta_exists_corrected n hn hlogn
  have h := TaoFivePrimes.rosser_schoenfeld_totient_lemma15_corrected n y (by omega) h1 h2 h3 h4
  have e : (2.50637 : ℝ) / Real.log (Real.log (n : ℝ))
      - 5 / (2 * Real.log (Real.log (n : ℝ)))
      = 0.00637 / Real.log (Real.log (n : ℝ)) := by
    field_simp
    ring
  have h0 : (0 : ℝ) ≤ 0.00637 / Real.log (Real.log (n : ℝ)) := by positivity
  linarith [e, h0]

#print axioms solution
