-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ReducedCutLength_intersectionNumber_baseChange_461afd068e57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:41.645192+00:00
-- url     : https://prove2.me/submissions/935b1d59-e8b2-4dd3-b81c-e2f83b756ec4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_eq_finsum_46067e88fe10

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace ReducedCutLength
theorem _root_.solution : ReducedCutLength.Statement :=
  fun _ _ _ I x Q _ hI hx hQ => ReducedCut.length_eq_finsum I x Q hI hx hQ
end ReducedCutLength
end GroundTheory.Heights₂.Heights.Inter
