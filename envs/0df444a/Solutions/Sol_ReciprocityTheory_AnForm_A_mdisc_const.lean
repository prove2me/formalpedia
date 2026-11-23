-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:08.555984+00:00
-- url     : https://prove2.me/submissions/677d7faa-f61a-43b5-b5fd-4f0f2cafcfa5

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A : Matrix (Fin D) (Fin D) ℂ) : mdisc (fun _ => A) = A.det := by
  rw [mdisc_eq_sum_perm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp
  rfl
end ReciprocityTheory.AnForm.A
