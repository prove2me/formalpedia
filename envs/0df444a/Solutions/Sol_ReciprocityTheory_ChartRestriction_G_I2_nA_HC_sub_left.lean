-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:16.174703+00:00
-- url     : https://prove2.me/submissions/0221b54b-f802-46d2-a32b-8a9d8b94464c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_sub_left

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
theorem _root_.solution (u v w : Fin n → EuclideanSpace ℂ ι) : HC (u - v) w = HC u w - HC v w := by
  simp [HC, nA_Hf_sub_left, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.G.I2
