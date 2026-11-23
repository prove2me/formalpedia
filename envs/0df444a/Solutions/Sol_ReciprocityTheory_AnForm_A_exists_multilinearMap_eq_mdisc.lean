-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:48.470416+00:00
-- url     : https://prove2.me/submissions/c16bcf51-0bbe-4b12-b7a4-c4e41d7f14d1

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
section
namespace ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
private lemma mdiscML_apply (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : mdiscML A = mdisc A := by
  rw [mdisc_eq_sum_perm, mdiscML, _root_.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  rw [← Matrix.det_transpose]
  rfl
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution :
    ∃ M : MultilinearMap ℂ (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ, ⇑M = mdisc := by
  exact ⟨mdiscML, funext mdiscML_apply⟩
end ReciprocityTheory.AnForm.A
