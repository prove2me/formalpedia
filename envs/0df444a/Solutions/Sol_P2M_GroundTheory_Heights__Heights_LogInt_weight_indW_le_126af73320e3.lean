-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_le_126af73320e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:00.45348+00:00
-- url     : https://prove2.me/submissions/bd02bcc8-3a04-4d10-9761-dd68a78c8311

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
theorem _root_.solution (p : ι → Prop) [DecidablePred p] (m : ι →₀ ℕ) :
    Finsupp.weight (indW p) m ≤ m.sum fun _ e => e := by
  rw [weight_indW, Finsupp.sum]
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp
end GroundTheory.Heights₂.Heights.LogInt
