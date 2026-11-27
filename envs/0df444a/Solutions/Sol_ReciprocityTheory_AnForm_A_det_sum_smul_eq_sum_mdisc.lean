-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_sum_smul_eq_sum_mdisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:27.381701+00:00
-- url     : https://prove2.me/submissions/1785b56d-a768-4dfc-94b4-f1d67f4713c7

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const
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
theorem _root_.solution {m : ℕ} (c : Fin m → ℂ)
    (A : Fin m → Matrix (Fin D) (Fin D) ℂ) :
    (∑ j, c j • A j).det = ∑ f : Fin D → Fin m, (∏ k, c (f k)) * mdisc (A ∘ f) := by
  rw [← mdisc_const, ← mdiscML_apply, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have := MultilinearMap.map_smul_univ (mdiscML (D := D)) (fun i => c (f i)) (fun i => A (f i))
  rw [this, smul_eq_mul, mdiscML_apply]
  rfl
end ReciprocityTheory.AnForm.A
