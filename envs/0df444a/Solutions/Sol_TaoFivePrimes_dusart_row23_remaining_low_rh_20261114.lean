-- Prove2me | solution 1 for TaoFivePrimes.dusart_row23_remaining_low_rh_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:41.242565+00:00
-- url     : https://prove2.me/submissions/621f7916-538a-48d3-aad8-259a6a8caf4d
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

theorem solution : ∀ ρ : NontrivialZetaZero,
  (((224/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
   ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) → ρ.val.re = 1/2 :=
  fun ρ _ =>
    riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
      ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2
