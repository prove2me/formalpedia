-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_sub_sub_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:02.127401+00:00
-- url     : https://prove2.me/submissions/93bdcad1-9e08-494d-a8b4-22fff0d3ca2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_sub_right
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
    (HC (v - a) (v - a)).re = (HC v v).re - 2 * (HC v a).re + (HC a a).re := by
  rw [nA_HC_sub_left, nA_HC_sub_right, nA_HC_sub_right, Complex.sub_re, Complex.sub_re,
    Complex.sub_re, nA_HC_re_symm v a]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
