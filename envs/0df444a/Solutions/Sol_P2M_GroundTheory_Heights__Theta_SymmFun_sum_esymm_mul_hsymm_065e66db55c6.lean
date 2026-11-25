-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_sum_esymm_mul_hsymm_065e66db55c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:44.941985+00:00
-- url     : https://prove2.me/submissions/987957e8-5434-4262-be09-77d53897a8dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SymmFun
open MvPolynomial Finset
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Theta.SymmFun
theorem _root_.solution (x : σ → ℂ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1), (-1) ^ s * eval x (esymm σ ℂ s) * eval x (hsymm σ ℂ (m - s)) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff m) (prod_one_sub_mul_hSeries x)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) *
      PowerSeries.coeff b (hSeries x))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_prod_one_sub, hSeries, PowerSeries.coeff_mk]
end GroundTheory.Heights₂.Theta.SymmFun
