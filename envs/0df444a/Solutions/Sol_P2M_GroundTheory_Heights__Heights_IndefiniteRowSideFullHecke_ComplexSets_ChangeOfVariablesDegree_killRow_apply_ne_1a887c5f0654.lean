-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_killRow_apply_ne_1a887c5f0654
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:10.054387+00:00
-- url     : https://prove2.me/submissions/ae224cfb-b81b-4152-ada2-dd8c6ea530b4

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
theorem _root_.solution {i k : Fin n} (h : k ≠ i) (M : Fin n → Fin n → ℝ) :
    killRow i M k = M k := by
  simp [killRow, h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
