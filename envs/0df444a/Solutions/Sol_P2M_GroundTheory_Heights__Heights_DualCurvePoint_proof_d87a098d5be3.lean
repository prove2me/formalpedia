-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePoint_proof_d87a098d5be3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:01:17.580671+00:00
-- url     : https://prove2.me/submissions/6f3d412c-7143-4e9f-a64d-e74603332684

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_numberField_coords_38ed536ee690

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DualCurvePoint
theorem _root_.solution : DualCurvePoint.Statement := by
  intro K _ _ i F T _ _ b W hW hle
  obtain ⟨L, _, _, z, t0, hz, rfl⟩ := DualCurvePointAlt.exists_numberField_coords W hW
  obtain ⟨_, v, hv, hvz⟩ := DualCurvePointAlt.exists_point b z t0 hz hle
  exact ⟨L, inferInstance, inferInstance, inferInstance, v, hv, by rw [hvz]⟩
end DualCurvePoint
end GroundTheory.Heights₂.Heights
