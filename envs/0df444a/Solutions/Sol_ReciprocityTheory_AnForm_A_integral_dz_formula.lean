-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_dz_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:40.356899+00:00
-- url     : https://prove2.me/submissions/82c01c39-f07a-46c6-99ea-bb08e0ba737d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrable_fderiv_apply_of_cs
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_fderiv_apply_of_cs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : IntegralDzStatement := by
  intro D j g hg hcs
  have h1 := integrable_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have h2 := integrable_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  have i1 := integral_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have i2 := integral_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  constructor
  · unfold dz
    rw [integral_div, integral_sub h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp
  · unfold dzb
    rw [integral_div, integral_add h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp
end ReciprocityTheory.AnForm.A
