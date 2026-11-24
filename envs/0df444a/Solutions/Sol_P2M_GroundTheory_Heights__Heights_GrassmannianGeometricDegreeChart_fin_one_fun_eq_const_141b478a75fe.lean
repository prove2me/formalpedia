-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_fin_one_fun_eq_const_141b478a75fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:05.183289+00:00
-- url     : https://prove2.me/submissions/7027aba7-2eb5-4e50-b613-2f3e6d276fa0

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
theorem _root_.solution {α : Type*} (i : Fin 1 → α) : (fun _ => i 0) = i :=
  funext fun k => congrArg i (Subsingleton.elim 0 k)
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
