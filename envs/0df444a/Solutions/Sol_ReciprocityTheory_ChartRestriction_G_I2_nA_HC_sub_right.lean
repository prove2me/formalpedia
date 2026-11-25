-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:50.130801+00:00
-- url     : https://prove2.me/submissions/2b8407a1-505c-49fb-b3ce-7fed3424ca26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_sub_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (u v w : Fin n → EuclideanSpace ℂ ι) : HC u (v - w) = HC u v - HC u w := by
  simp [HC, nA_Hf_sub_right, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.G.I2
