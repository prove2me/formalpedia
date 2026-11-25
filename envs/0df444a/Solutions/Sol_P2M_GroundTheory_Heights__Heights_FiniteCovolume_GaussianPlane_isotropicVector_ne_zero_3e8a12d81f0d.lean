-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_isotropicVector_ne_zero_3e8a12d81f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:17:02.034266+00:00
-- url     : https://prove2.me/submissions/907fb160-6044-49a1-b806-5dbd56297120

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution : v0 ≠ 0 := fun h => one_ne_zero (congrFun h 0)
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
