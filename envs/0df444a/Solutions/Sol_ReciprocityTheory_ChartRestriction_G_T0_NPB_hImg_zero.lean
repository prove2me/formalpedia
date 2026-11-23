-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.591563+00:00
-- url     : https://prove2.me/submissions/0ad90594-4ea2-4d6d-bfde-e56ce1acd057

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (j : Fin (N + 1)) :
    hImg (K := K) (D := D) ((0 : Fin (D + 1)), j) = X (Fin.castAdd D j) := by
  simp [hImg]
end ReciprocityTheory.ChartRestriction.G.T0.NPB
