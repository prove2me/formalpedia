-- Prove2me | solution 1 for TaoFivePrimes.row23_low_gap_cut_20261116
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T20:14:26.777824+00:00
-- url     : https://prove2.me/submissions/1c69ef05-17cf-4180-af3b-8c1ff16dc97a

import Definitions.Def_row23_rh_supp_RHRow23LowGap66388
open Complex DusartSmoothing
noncomputable section
theorem solution
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (|ρ.val.im| < (14:ℝ) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  exact DusartLegendreSmoothing.Moment380k.row23_of_low_sum_low_gaps_and_positive_tail_66388 hFine hGap hTail x hx
