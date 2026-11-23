-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_mpSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:22.541126+00:00
-- url     : https://prove2.me/submissions/4f0f88e0-f666-4828-aa50-51c2187e5760

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
theorem _root_.solution (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0)
      (blockSphereProb (D + 1) n) ((sphereProb n).prod (blockSphereProb D n)) := by
  unfold blockSphereProb
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => sphereProb n) 0
end ReciprocityTheory.ChartRestriction.G.T0
