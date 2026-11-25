-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_sum_perm_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:01.905931+00:00
-- url     : https://prove2.me/submissions/f8f93551-9c60-4ee9-b669-61a9c622614b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pmWt_comp_perm
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_comp_bijective

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
    (D.factorial : ℂ) * ∑ g : Fin D → Fin D × ι,
        (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) =
      ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) := by
  have hcard : (D.factorial : ℂ) = ∑ _τ : Equiv.Perm (Fin D), (1 : ℂ) := by
    simp [Fintype.card_perm]
  rw [hcard, Finset.sum_mul]
  simp only [one_mul]
  rw [Finset.sum_congr rfl fun τ _ => (Fintype.sum_bijective _ (pm_comp_bijective (ι := ι) τ)
    (fun g => (pmWt (g ∘ τ) : ℂ) * ((pmGmat w (g ∘ τ)).det *
      ∏ a, star (w ((g ∘ τ) a).1 ((g ∘ τ) a).2 a)))
    (fun g => (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)))
    fun _ => rfl).symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hsub : ∀ τ : Equiv.Perm (Fin D), pmGmat w (g ∘ τ) = (pmGmat w g).submatrix id τ :=
    fun τ => rfl
  have hstar : star (pmGmat w g).det = ∑ τ : Equiv.Perm (Fin D),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ a, star (w (g (τ a)).1 (g (τ a)).2 a) := by
    rw [← det_conjTranspose, det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [conjTranspose_apply, pmGmat, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  simp only [pmWt_comp_perm, hsub, det_permute', Function.comp_apply]
  rw [hstar, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end ReciprocityTheory.AnForm.A
