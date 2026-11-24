-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:42.143573+00:00
-- url     : https://prove2.me/submissions/465b255e-02b7-432c-9a95-c3f4b18498a2

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
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (A ∘ σ) = mdisc A := by
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => (Matrix.of fun i j => A (τ j) i j).det)
end ReciprocityTheory.AnForm.A
