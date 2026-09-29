-- Prove2me | solution 1 for TaoFivePrimes.vinogradov_odd_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T02:41:46.310912+00:00
-- url     : https://prove2.me/submissions/28562782-01ad-456d-9f3b-f2b897348883

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51VinogradovSharp
import Theorems.Thm_TaoFivePrimes_vinogradov_block_coprime

open Finset
open TaoFivePrimesVinogradovSharp

/-- Corollary 3.5 at the sharp block count, from the corrected block estimate. -/
theorem solution
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A alpha beta theta x y : ℝ) (a' : ℤ) (hA : 0 ≤ A)
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha : 2 * alpha = (a' : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ z ∈ (TaoFivePrimesVinogradovSharp.zIoc x y).filter (fun z => Odd z),
        TaoFivePrimesVinogradovSharp.vmin A B alpha theta z)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  have hR : vRhs q A B = 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
    unfold vRhs
    norm_num
  have hbb : blockBound q A B (2 * alpha) (Real.pi * alpha + theta) ((x - 1) / 2) ((y - 1) / 2) :=
    blockBound_of_int_block q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2) hA hB
      (fun m => by
        simpa [vmin, hR] using
          (TaoFivePrimes.vinogradov_block_coprime B hB q hq A (2 * alpha) beta
            (Real.pi * alpha + theta) a' hA ha'q halpha hbeta m))
  have hodd := odd_block_from_block q A B alpha theta x y hbb hwidth
  simpa [hR] using hodd
