-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_PFSum_of_genDeg_0a155684cf4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:34.163283+00:00
-- url     : https://prove2.me/submissions/f2017f06-bd07-40a4-9b7e-d44019bb4e28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_OfGenDeg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_inl


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
theorem _root_.solution (h : PushforwardArithIntersection.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement at h
  intro I hI K _ ι _ K₂ _ ι₂ _ P₂ d G J L L' hP₂ hP hJ hL hLL'
  exact h I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV P₂ d G J L L' isBlockMap_inl hP₂ hP hJ hL hLL'
end PFSum
end GroundTheory.Heights₂.Heights.Targets
