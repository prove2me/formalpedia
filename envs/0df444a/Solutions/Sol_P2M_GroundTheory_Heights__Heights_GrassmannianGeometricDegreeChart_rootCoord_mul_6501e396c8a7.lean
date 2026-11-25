-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:46.34621+00:00
-- url     : https://prove2.me/submissions/10a65bd3-d1df-41cb-9b8b-0d82f24703d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a

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
theorem _root_.solution (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (ht : z a0 ≠ 0) :
    (fun p => rootCoord (chartPt z) p * z a0) = z := by
  funext p
  obtain ⟨k, I⟩ := p
  obtain rfl : k = 0 := Subsingleton.elim _ _
  conv_rhs => rw [eq_single1 I]
  simp only [rootCoord, colsOf, onePipe, Matrix.det_unique, Matrix.submatrix_apply, Matrix.of_apply, id]
  generalize I.1.orderEmbOfFin I.2 0 = c
  refine Fin.addCases (fun a => ?_) (fun b => ?_) c
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [Fin.append_left]
    rw [show (default : Fin 1) = 0 from rfl, Matrix.one_apply_eq, one_mul]
    rfl
  · simp only [Fin.append_right, chartPt]
    exact div_mul_cancel₀ _ ht
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
