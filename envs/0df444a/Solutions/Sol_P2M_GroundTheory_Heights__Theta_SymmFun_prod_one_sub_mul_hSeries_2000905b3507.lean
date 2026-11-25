-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SymmFun_prod_one_sub_mul_hSeries_2000905b3507
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:03.14951+00:00
-- url     : https://prove2.me/submissions/f861dc68-3a9c-4a47-97f3-cf3237df0fb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_hSeries_eq_prod_5197623120c0
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SymmFun_one_sub_mul_geom_54d99a6e3807

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
    (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) * hSeries x = 1 := by
  rw [hSeries_eq_prod, ← Finset.prod_mul_distrib]
  simp [one_sub_mul_geom]
end GroundTheory.Heights₂.Theta.SymmFun
