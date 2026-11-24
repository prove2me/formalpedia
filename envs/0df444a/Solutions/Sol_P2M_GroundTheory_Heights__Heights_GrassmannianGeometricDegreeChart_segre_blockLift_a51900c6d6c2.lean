-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.8201+00:00
-- url     : https://prove2.me/submissions/c25c8dd1-6e26-494a-b50a-d15eb8e8e60d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b

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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution (x : PlIdx 1 n → ℂ) :
    segre (ι := plBlocks 1 1 n) (blockLift x) = fun i => x (i 0) := by
  funext i
  rw [segre_eq]
  rfl
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
