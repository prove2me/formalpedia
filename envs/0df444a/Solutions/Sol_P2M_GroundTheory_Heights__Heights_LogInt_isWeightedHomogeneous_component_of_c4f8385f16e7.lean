-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:18.506812+00:00
-- url     : https://prove2.me/submissions/db34f7a0-c03a-4df6-aa1d-c1825f155554

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
theorem _root_.solution (w w' : ι → ℕ) (g : MvPolynomial ι ℂ) (d e : ℕ)
    (h : IsWeightedHomogeneous w g e) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w' d g) e := by
  intro m hm
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact h hm
  · exact absurd rfl hm
end GroundTheory.Heights₂.Heights.LogInt
