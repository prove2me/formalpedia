-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfPoint_proof_a8eb2a624e05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:55.410972+00:00
-- url     : https://prove2.me/submissions/551452cb-fd6a-457d-9f75-50effc5d8b69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_heightOfPoint_e175e6500c66

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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open HeightOfPointAlt
namespace GroundTheory.Heights₂.Heights
namespace HeightOfPoint
theorem _root_.solution (_h1 : GaussNormBasic.Statement) : HeightOfPoint.Statement :=
  heightOfPoint
end HeightOfPoint
end GroundTheory.Heights₂.Heights
