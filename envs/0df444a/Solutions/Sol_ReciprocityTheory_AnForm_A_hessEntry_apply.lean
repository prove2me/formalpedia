-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessEntry_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:59.967542+00:00
-- url     : https://prove2.me/submissions/b0d4368a-960c-461b-b55e-83ab0aebd6c0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_evalL_apply

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
theorem _root_.solution {D : ℕ} (a b : Fin D) (H : BilinSp D) :
    hessEntry a b H =
      ((H (Pi.single a 1) (Pi.single b 1) +
          H (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℝ) +
        Complex.I * ((H (Pi.single a 1) (Complex.I • Pi.single b 1) -
          H (Complex.I • Pi.single a 1) (Pi.single b 1) : ℝ))) / 4 := by
  simp only [hessEntry, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, evalL_apply,
    smul_eq_mul]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
