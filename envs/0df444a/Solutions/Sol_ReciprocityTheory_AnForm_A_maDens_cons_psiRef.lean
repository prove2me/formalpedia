-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_psiRef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:50.431842+00:00
-- url     : https://prove2.me/submissions/ab5114ea-dd6f-4a0d-ba06-d61b1ae35ef5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_cons
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_sum_normSq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_eq_sum


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
theorem _root_.solution (h : (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons h (psiRef n)) z = kDens n *
      (∑ j, ∑ k, hessC h z j k *
        mixedCof (fun _ : Fin n => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) j k).re := by
  unfold maDens
  rw [hessC_cons]
  have hp : (fun k => hessC (psiRef n k) z) = fun _ => 1 := funext fun k => hessC_sum_normSq z
  rw [hp, mdisc_cons_eq_sum]
  unfold kDens
  rfl
end ReciprocityTheory.AnForm.A
