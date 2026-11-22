-- Prove2me | solution 1 for TaoFivePrimes.dusart_row23_conditional_67156_20261114
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T23:06:38.203174+00:00
-- url     : https://prove2.me/submissions/9464a570-3eb8-46b2-bb65-4095f1dbeeff

import Definitions.Def_row23_rh_supp_RHRow23LowSlabTwentyThird66388
import Theorems.Thm_TaoFivePrimes_rh_positive_121_to_67156_20261114
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
open Complex DusartSmoothing DusartLegendreSmoothing.Moment380k
theorem solution
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (((224/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (67156 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  apply row23_of_low_sum_after_twentythird_slab_and_positive_tail_66388 hFine hGap ?_ x hx
  intro s hs ha hb
  by_cases hm : s.im ≤ (67156 + 25/8192:ℝ)
  · apply TaoFivePrimes.rh_positive_121_to_67156_20261114 s hs.1 hs.2.1 hs.2.2 ?_ ?_ hm <;> linarith
  · exact hTail s hs (lt_of_not_ge hm) hb

