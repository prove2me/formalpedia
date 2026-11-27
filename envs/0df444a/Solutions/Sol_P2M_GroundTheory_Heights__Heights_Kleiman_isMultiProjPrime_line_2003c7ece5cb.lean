-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_line_2003c7ece5cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:55.871333+00:00
-- url     : https://prove2.me/submissions/ae16f3b8-0f0b-436e-829f-8799f080be88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isMultiProjPrime_primeOfOne_739683a29f58

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution :
    NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) (lineX k)) :=
  isMultiProjPrime_primeOfOne _ fun h => lineX_ne_zero k 0 (congrFun h 0)
end GroundTheory.Heights₂.Heights.Kleiman
