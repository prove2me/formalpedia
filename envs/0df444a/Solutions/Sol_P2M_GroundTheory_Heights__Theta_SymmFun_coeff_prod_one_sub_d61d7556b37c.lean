-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_coeff_prod_one_sub_d61d7556b37c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:39.016799+00:00
-- url     : https://prove2.me/submissions/5533762a-2689-413f-81a6-70abcde78cab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous

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
theorem _root_.solution (x : σ → ℂ) (s : ℕ) :
    PowerSeries.coeff s (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) =
      (-1) ^ s * eval x (esymm σ ℂ s) := by
  have h : ∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X) =
      ∏ i, (PowerSeries.C (-x i) * PowerSeries.X + 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_neg, neg_mul, ← sub_eq_neg_add]
  rw [h, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [esymm, map_sum, Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.powersetCard_eq_filter]
  refine Finset.sum_congr (by ext t; simp [eq_comm]) fun t ht => ?_
  simp only [Finset.mem_filter] at ht
  rw [map_prod]
  simp only [eval_X]
  have hneg : ∀ i, -x i = (-1) * x i := fun i => by ring
  simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, ht.2]
end GroundTheory.Heights₂.Theta.SymmFun
