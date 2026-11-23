-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:03.106989+00:00
-- url     : https://prove2.me/submissions/3f2e429e-ebed-418b-a6de-6f342f27edb8

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (i : Fin D) (j : Fin (N + 1)) :
    hImg (K := K) (i.succ, j) = X (Fin.natAdd (N + 1) i) * C (X (i, j)) := by
  simp [hImg]
end ReciprocityTheory.ChartRestriction.G.T0.NPB
