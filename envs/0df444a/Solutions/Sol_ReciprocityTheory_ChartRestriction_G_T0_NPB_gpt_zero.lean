-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:37.272344+00:00
-- url     : https://prove2.me/submissions/5913b275-5875-4126-83f4-501123852017

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (j : Fin (N + 1)) :
    gpt tt y (0, j) = y (Fin.castAdd D j) := by simp [gpt]
end ReciprocityTheory.ChartRestriction.G.T0.NPB
