-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_PFSum_of_found_3b9b02eb6394
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:48.004313+00:00
-- url     : https://prove2.me/submissions/9d1e7270-976c-45f0-812c-d301a5d9802b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_OfGenDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PFSum_of_genDeg_0a155684cf4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_proof_f5a8d74a2887
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arithVarZero_56f17dda19d2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Targets
namespace PFSum
theorem _root_.solution (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement :=
  PFSum.of_genDeg (PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt)
end PFSum
end GroundTheory.Heights₂.Heights.Targets
