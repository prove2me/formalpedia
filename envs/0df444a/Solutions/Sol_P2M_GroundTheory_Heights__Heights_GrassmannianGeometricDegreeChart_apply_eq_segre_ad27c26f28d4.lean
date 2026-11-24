-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:31.843603+00:00
-- url     : https://prove2.me/submissions/edf0e1b4-8886-48c3-a24b-f5a2eca5dba7

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
theorem _root_.solution (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (p : Σ _ : Fin 1, PlIdx 1 n) :
    z p = segre (ι := plBlocks 1 1 n) z (fun _ => p.2) := by
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  rw [segre_eq]
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
