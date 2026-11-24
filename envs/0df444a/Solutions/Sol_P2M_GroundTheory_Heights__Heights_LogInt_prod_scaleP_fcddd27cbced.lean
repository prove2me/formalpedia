-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_prod_scaleP_fcddd27cbced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:00.309798+00:00
-- url     : https://prove2.me/submissions/d20831b9-d284-4bb0-9179-93a3de1bc2eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) (m : ι →₀ ℕ) :
    ∏ i ∈ m.support, scaleP p a u i ^ m i =
      a ^ Finsupp.weight (indW p) m * ∏ i ∈ m.support, u i ^ m i := by
  rw [weight_indW, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : p i <;> simp [scaleP, h, mul_pow]
end GroundTheory.Heights₂.Heights.LogInt
