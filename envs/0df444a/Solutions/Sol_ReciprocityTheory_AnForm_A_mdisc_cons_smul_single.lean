-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_cons_smul_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:33.536302+00:00
-- url     : https://prove2.me/submissions/06b708d7-39b9-421a-8394-244e6d458cb3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedCof_diag


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
theorem _root_.solution (i : Fin (n + 1)) (c : ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • Matrix.single i i 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * ((1 / ((n : ℂ) + 1)) * mdisc (fun k => (B k).submatrix i.succAbove i.succAbove)) := by
  have h := mdisc_update_smul
    (Fin.cons (Matrix.single i i 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 c
    (Matrix.single i i 1)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  rw [h]
  have h2 := mixedCof_diag B i
  simp only [mixedCof] at h2
  rw [h2]
  push_cast
  ring
end ReciprocityTheory.AnForm.A
