-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_sum_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:52.924344+00:00
-- url     : https://prove2.me/submissions/1ad3b6ba-eb55-4fda-a555-288e4b2d0c86

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_swap_row
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_expand

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
    (k : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ j a b, S j a b = S a j b) :
    ∑ j, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S j)) = 0 := by
  rw [Finset.sum_congr rfl fun j _ => mdisc_update_expand _ q (S j)]
  have h2 : ∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q
      (Matrix.single a b 1)) = -∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update
      (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [hS a j b, mdisc_swap_row A p q hpq j k a b]
    ring
  linear_combination (1 / 2 : ℂ) * h2
end ReciprocityTheory.AnForm.A
