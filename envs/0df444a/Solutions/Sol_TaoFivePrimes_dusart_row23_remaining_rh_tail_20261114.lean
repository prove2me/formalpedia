-- Prove2me | solution 1 for TaoFivePrimes.dusart_row23_remaining_rh_tail_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:39.782801+00:00
-- url     : https://prove2.me/submissions/b3683701-4e37-4266-871a-953df8b0854b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ZeroSeries
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open Complex DusartSmoothing
noncomputable section
namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes

theorem solution : ∀ s : ℂ, RvM.IsNontrivialZero s → (67156 + 25/8192:ℝ) < s.im →
  s.im ≤ (380000:ℝ) → s.re = 1/2 :=
  fun s hs _ _ =>
    riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hs.1 hs.2.1 hs.2.2
