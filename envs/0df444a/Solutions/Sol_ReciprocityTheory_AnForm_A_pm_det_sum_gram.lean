-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_det_sum_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:49.39359+00:00
-- url     : https://prove2.me/submissions/1d382835-974f-412b-a97e-75bbd245f02a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_gram_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) :
    (∑ k ∈ S, pmGram w k).det = ∑ g : Fin D → Fin D × ι,
      (if ∀ a, (g a).1 ∈ S then (1 : ℂ) else 0) *
        ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
  simp only [det_apply, pm_sum_gram_apply]
  simp only [Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, pmGmat, Matrix.of_apply, Finset.prod_boole,
    Finset.mem_univ, true_imp_iff, Units.smul_def, zsmul_eq_mul]
  ring
end ReciprocityTheory.AnForm.A
