-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:09.026224+00:00
-- url     : https://prove2.me/submissions/923dcc57-3b87-4525-ac1e-e5bab47d3e81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart

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
theorem _root_.solution (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (i : Fin 1 → PlIdx 1 n) :
    segre (ι := plBlocks 1 1 n) z i = z ⟨0, i 0⟩ := by
  simp [segre]
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
