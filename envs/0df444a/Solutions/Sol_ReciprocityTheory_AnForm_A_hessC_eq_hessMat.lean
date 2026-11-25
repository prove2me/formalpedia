-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_eq_hessMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:03.576376+00:00
-- url     : https://prove2.me/submissions/346c816e-b30d-468d-b9fb-69b13b015335

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessEntry_apply
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessMat_apply

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
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    hessC φ y = hessMat (fderiv ℝ (fderiv ℝ φ) y) := by
  ext a b
  rw [hessMat_apply, hessEntry_apply]
  rfl
end ReciprocityTheory.AnForm.A
