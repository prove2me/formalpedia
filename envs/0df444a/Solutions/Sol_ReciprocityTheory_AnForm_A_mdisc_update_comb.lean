-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_update_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:42.46686+00:00
-- url     : https://prove2.me/submissions/5e655cb5-8314-413d-8546-fa59a2c5c194

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul


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
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D) (c d : ℂ)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q (c • B + d • C)) =
      c * mdisc (Function.update A q B) + d * mdisc (Function.update A q C) := by
  rw [mdisc_update_add, mdisc_update_smul, mdisc_update_smul]
end ReciprocityTheory.AnForm.A
