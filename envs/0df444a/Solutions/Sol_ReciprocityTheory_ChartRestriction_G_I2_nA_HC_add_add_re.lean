-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_add_add_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:35.507255+00:00
-- url     : https://prove2.me/submissions/87b1c059-ef7d-485c-80cf-aba21b97dc4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_re_symm

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
theorem _root_.solution (v a : Fin n → EuclideanSpace ℂ ι) :
    (HC (v + a) (v + a)).re = (HC v v).re + 2 * (HC v a).re + (HC a a).re := by
  rw [nA_HC_add_left, nA_HC_add_right, nA_HC_add_right, Complex.add_re, Complex.add_re,
    Complex.add_re, nA_HC_re_symm v a]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
