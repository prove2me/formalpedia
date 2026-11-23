-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_blockPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:36.85186+00:00
-- url     : https://prove2.me/submissions/84750e88-4167-414b-806d-039cfdf2a3b0

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D n : ℕ} (z : BlockSphere (D + 1) n) :
    blockPoint z = hintPt (spherePoint (z 0)) (fun i : Fin D => z i.succ) := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero => simp [blockPoint, hintPt]
  | succ i => simp [blockPoint, hintPt]
end ReciprocityTheory.ChartRestriction.G.T0
