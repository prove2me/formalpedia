-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.minorDens_psiRef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:36.742909+00:00
-- url     : https://prove2.me/submissions/5b3e17bc-66b5-468b-b848-9d166f062bb6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_sum_normSq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const


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
theorem _root_.solution (i : Fin (n + 1)) (z : Fin (n + 1) → ℂ) : minorDens i (psiRef n) z = 1 := by
  have hp : ∀ k, hessC (psiRef n k) z = 1 := fun k => hessC_sum_normSq z
  simp only [minorDens, hp]
  rw [Matrix.submatrix_one _ (Fin.succAbove_right_injective), mdisc_const]
  simp
end ReciprocityTheory.AnForm.A
