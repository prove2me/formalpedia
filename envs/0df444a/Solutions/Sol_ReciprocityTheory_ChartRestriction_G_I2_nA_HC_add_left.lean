-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:41.988966+00:00
-- url     : https://prove2.me/submissions/72518961-fc81-4e31-ac10-3ef358a87e12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_add_left

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
theorem _root_.solution (u v w : Fin n → EuclideanSpace ℂ ι) : HC (u + v) w = HC u w + HC v w := by
  simp [HC, nA_Hf_add_left, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.I2
