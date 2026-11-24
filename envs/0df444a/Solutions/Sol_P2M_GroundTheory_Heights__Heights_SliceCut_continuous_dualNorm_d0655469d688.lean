-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:04.215102+00:00
-- url     : https://prove2.me/submissions/01d88691-96c3-495b-b735-4836254ebbc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)
namespace GroundTheory.Heights₂.Heights.SliceCut
theorem _root_.solution : Continuous h.dualNorm := by
  unfold HermNorm.dualNorm
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).norm.pow 2
end GroundTheory.Heights₂.Heights.SliceCut
