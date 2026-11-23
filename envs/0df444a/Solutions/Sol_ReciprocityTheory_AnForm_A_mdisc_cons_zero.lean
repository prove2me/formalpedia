-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_cons_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:18.020217+00:00
-- url     : https://prove2.me/submissions/8e71feef-7ea2-41db-899e-e2d44912f76a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
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
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  have h := mdisc_update_smul
    (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0 0
  simpa [Fin.update_cons_zero] using h
end ReciprocityTheory.AnForm.A
