-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:07.929031+00:00
-- url     : https://prove2.me/submissions/cda62b91-fbff-454e-bfd9-9693081ced96

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
theorem _root_.solution : Fintype.card (Fin 1 → PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
