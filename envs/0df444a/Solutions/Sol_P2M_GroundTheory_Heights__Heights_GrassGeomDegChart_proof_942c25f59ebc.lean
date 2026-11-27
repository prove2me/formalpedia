-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassGeomDegChart_proof_942c25f59ebc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:25.493206+00:00
-- url     : https://prove2.me/submissions/77b25070-4848-4406-8158-a5eff60b55ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f

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
open GrassmannianGeometricDegreeChart
namespace GroundTheory.Heights₂.Heights
namespace GrassGeomDegChart
theorem _root_.solution : GrassGeomDegChart.Statement := by
  intro n
  have hex := exists_good n
  obtain ⟨B, hB, hval⟩ := ptsIntegralAt_eq hex.choose_spec
  refine ⟨B, hB, ?_⟩
  unfold geomDeg ptsIntegral
  rw [dif_pos hex]
  exact hval
end GrassGeomDegChart
end GroundTheory.Heights₂.Heights
