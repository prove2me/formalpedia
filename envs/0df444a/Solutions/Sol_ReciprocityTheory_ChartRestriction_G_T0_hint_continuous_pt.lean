-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_continuous_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:48.244336+00:00
-- url     : https://prove2.me/submissions/44de2e8e-3c1f-4f5a-910c-c91c10b09e60

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
theorem _root_.solution {D n : ℕ} (t0 : Fin n → ℂ) :
    Continuous fun z : BlockSphere D n => hintPt t0 z := by
  apply continuous_pi
  rintro ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    simp only [hintPt, Fin.cases_zero]
    exact continuous_const
  | succ i =>
    simp only [hintPt, Fin.cases_succ]
    unfold spherePoint
    fun_prop
end ReciprocityTheory.ChartRestriction.G.T0
