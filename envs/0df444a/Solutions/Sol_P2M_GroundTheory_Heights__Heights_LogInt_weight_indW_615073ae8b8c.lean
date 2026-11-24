-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_weight_indW_615073ae8b8c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:21.753176+00:00
-- url     : https://prove2.me/submissions/719f959b-a823-41e1-a3d6-5bee514e9235

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly

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
    Finsupp.weight (indW p) m = ∑ i ∈ m.support, if p i then m i else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [indW]
end GroundTheory.Heights₂.Heights.LogInt
