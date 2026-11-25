-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:47.972803+00:00
-- url     : https://prove2.me/submissions/99cce108-215a-4739-8ea6-e044d679e89a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_eq_zero_of_notMem
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_cons
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_zero

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
theorem _root_.solution {v : (Fin (n + 1) → ℂ) → ℝ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {z : Fin (n + 1) → ℂ} (hz : z ∉ tsupport v) : maDens (Fin.cons v φ) z = 0 := by
  unfold maDens
  rw [hessC_cons, hessC_eq_zero_of_notMem hz, mdisc_cons_zero]
  simp
end ReciprocityTheory.AnForm.A
