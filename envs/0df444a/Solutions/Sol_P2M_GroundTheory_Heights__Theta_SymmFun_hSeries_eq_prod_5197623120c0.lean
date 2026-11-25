-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:55.907394+00:00
-- url     : https://prove2.me/submissions/4693d38d-f6bb-4000-848c-c3c8acdae484

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_eval_hsymm_04c692b73247

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
theorem _root_.solution (x : σ → ℂ) :
    hSeries x = ∏ i, PowerSeries.mk fun k => x i ^ k := by
  ext b
  rw [hSeries, PowerSeries.coeff_mk, eval_hsymm, PowerSeries.coeff_prod]
  simp [PowerSeries.coeff_mk]
end GroundTheory.Heights₂.Theta.SymmFun
