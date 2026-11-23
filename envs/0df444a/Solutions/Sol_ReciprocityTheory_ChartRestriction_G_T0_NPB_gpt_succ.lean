-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:36.189439+00:00
-- url     : https://prove2.me/submissions/bbc23340-906d-41a2-9f20-e25905cfd031

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (i : Fin D)
    (j : Fin (N + 1)) : gpt tt y (i.succ, j) = y (Fin.natAdd (N + 1) i) * tt (i, j) := by simp [gpt]
end ReciprocityTheory.ChartRestriction.G.T0.NPB
