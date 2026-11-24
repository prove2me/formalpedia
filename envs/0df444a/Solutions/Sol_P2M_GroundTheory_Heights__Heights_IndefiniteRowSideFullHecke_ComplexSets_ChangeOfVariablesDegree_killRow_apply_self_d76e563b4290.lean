-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_self_d76e563b4290
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:10.630657+00:00
-- url     : https://prove2.me/submissions/1c4a7111-da6f-4af7-8e8d-03ee270d9030

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
theorem _root_.solution (i : Fin n) (M : Fin n → Fin n → ℝ) : killRow i M i = 0 := by
  simp [killRow]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
