-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_fderiv_eq_det_jacobian_2f5e8fc08a22
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:27.978832+00:00
-- url     : https://prove2.me/submissions/72062b65-ae4d-4841-baf8-341f4677d614

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
theorem _root_.solution (H : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    (fderiv ℝ H x).det = (Matrix.of (jacobian H x)).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
