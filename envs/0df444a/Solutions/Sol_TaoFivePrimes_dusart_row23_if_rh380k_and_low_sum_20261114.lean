-- Prove2me | solution 1 for TaoFivePrimes.dusart_row23_if_rh380k_and_low_sum_20261114
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-13T22:36:38.892904+00:00
-- url     : https://prove2.me/submissions/36800272-2706-4f95-8f92-e1b3864ec9e1

import Definitions.Def_row23_rh_supp_RHLocalRow23OfRH380kConditionalSum
set_option autoImplicit false
noncomputable section
open Complex DusartSmoothing
theorem solution
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hRH : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ (380000:ℝ) → ρ.val.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ) * x := by
  exact DusartLegendreSmoothing.Moment380k.row23_of_RH380k_and_low_sum hFine hRH x hx
