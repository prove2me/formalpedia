-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:08.967841+00:00
-- url     : https://prove2.me/submissions/d4849f4d-42b0-4f39-9209-a958ee6134b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (V : Fin n → Fin n → ℝ) (k : Fin n) (r : Fin n → ℝ) :
    Matrix.det (Matrix.of (Function.update V k r)) =
      ∑ l, r l * Matrix.det (Matrix.of (Function.update V k (Pi.single l 1))) := by
  have hr : r = ∑ l, r l • (Pi.single l 1 : Fin n → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [hr]
  change (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap V k
    (∑ l, r l • (Pi.single l 1 : Fin n → ℝ)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
