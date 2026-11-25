-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessCof_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:46.081776+00:00
-- url     : https://prove2.me/submissions/d49d1597-ba4e-45e0-a88f-ef68ec64b743

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_eq_hessMat

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
theorem _root_.solution {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (j k : Fin (n + 1)) :
    hessCof φ y j k = mdisc (Fin.cons (Matrix.single j k 1) fun i => hessMat (fderiv ℝ (fderiv ℝ (φ i)) y)) := by
  simp only [hessCof, mixedCof, hessC_eq_hessMat]
end ReciprocityTheory.AnForm.A
