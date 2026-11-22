-- Prove2me | solution 1 for TaoFivePrimes.row23_slab_thirteenth_cut_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T21:21:31.149033+00:00
-- url     : https://prove2.me/submissions/9b6d7430-c21f-4239-ba93-c4e3de0f8b7d

import Definitions.Def_row23_rh_supp_RHRow23LowSlabThirteenth66388
open Complex DusartSmoothing
noncomputable section
theorem solution
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (((214/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  exact DusartLegendreSmoothing.Moment380k.row23_of_low_sum_after_thirteenth_slab_and_positive_tail_66388 hFine hGap hTail x hx
