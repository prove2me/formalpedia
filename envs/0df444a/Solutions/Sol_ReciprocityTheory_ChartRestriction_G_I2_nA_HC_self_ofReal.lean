-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_self_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:58.393718+00:00
-- url     : https://prove2.me/submissions/2ffea46c-2d2a-4a1a-b9cb-00cd4c20d007

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_self_im

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
theorem _root_.solution (v : Fin n → EuclideanSpace ℂ ι) : HC v v = ((HC v v).re : ℂ) := by
  apply Complex.ext <;> simp [nA_HC_self_im]
end ReciprocityTheory.ChartRestriction.G.I2
