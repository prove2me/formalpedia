-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_mdisc_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:39.474142+00:00
-- url     : https://prove2.me/submissions/d39ec2d1-f21a-43e5-b40d-821e44c06ac9

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_det_sum_gram
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_alt
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_sum_perm_reindex

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
theorem _root_.solution (w : Fin D → ι → Fin D → ℂ) :
    mdisc (pmGram w) = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hD : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h1 : (D.factorial : ℂ) * mdisc (pmGram w) = ∑ g : Fin D → Fin D × ι,
      (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
    rw [mdisc, ← mul_assoc, mul_one_div_cancel hD, one_mul]
    simp only [pm_det_sum_gram, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← pm_sum_alt, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  have h2 := pm_sum_perm_reindex w
  rw [← h1] at h2
  have h3 : ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) =
      ((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  push_cast
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  push_cast at h3
  rw [← h3, ← h2]
  ring
end ReciprocityTheory.AnForm.A
