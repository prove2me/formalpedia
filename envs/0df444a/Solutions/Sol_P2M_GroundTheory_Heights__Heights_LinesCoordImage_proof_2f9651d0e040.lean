-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesCoordImage_proof_2f9651d0e040
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:23.169785+00:00
-- url     : https://prove2.me/submissions/8780af56-ce2c-4679-9adc-8c53c7eea7d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordImage

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
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace LinesCoordImage
theorem _root_.solution : LinesCoordImage.Statement := by
  intro K _ n m k B b c j
  funext l
  simp [coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂,
    Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
end LinesCoordImage
end GroundTheory.Heights₂.Heights
