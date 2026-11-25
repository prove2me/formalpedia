-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_sum_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:50.485199+00:00
-- url     : https://prove2.me/submissions/d1eaeb19-1c71-432c-8493-a3c28a0f4bfa

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDisc_transpose
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_sum_row
import Theorems.Thm_ReciprocityTheory_AnForm_A_update_transpose

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
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ k a b, S k a b = S b a k) :
    ∑ k, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S k)) = 0 := by
  have ht : ∀ k', mdisc (Function.update (Function.update A p (Matrix.single j k' 1)) q (S k')) =
      mdisc (Function.update (Function.update (fun r => (A r)ᵀ) p (Matrix.single k' j 1)) q (S k')ᵀ) := by
    intro k'
    rw [← mixedDisc_transpose, update_transpose, Matrix.transpose_single]
  rw [Finset.sum_congr rfl fun k' _ => ht k']
  exact mdisc_sum_row (fun r => (A r)ᵀ) p q hpq j (fun k' => (S k')ᵀ)
    (fun x a b => by simp only [Matrix.transpose_apply]; exact hS x b a)
end ReciprocityTheory.AnForm.A
