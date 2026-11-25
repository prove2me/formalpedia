-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:00.639904+00:00
-- url     : https://prove2.me/submissions/476f6ed0-c87d-4e11-aac4-69ccbb54b84c

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
theorem _root_.solution (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases k with _ | k
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero k), pow_succ, mul_comm, sub_self]
end GroundTheory.Heights₂.Theta.SymmFun
