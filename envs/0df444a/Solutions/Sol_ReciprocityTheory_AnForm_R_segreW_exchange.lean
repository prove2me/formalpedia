-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreW_exchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:56.854367+00:00
-- url     : https://prove2.me/submissions/f526f9b3-a79e-43ef-b3e6-6ed3cd330818

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_update_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_X
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_eq_of_segreMap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [DecidableEq K] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (p p' : (k : K) → ι k) (q : Σ k, ι k) :
    segreW P (Function.update p q.1 q.2) * segreW P (Function.update p' q.1 (p q.1)) =
      segreW P (Function.update p' q.1 q.2) * segreW P p := by
  obtain ⟨k, v⟩ := q
  simp only [segreW, ← map_mul]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, segreMap_X]
  rw [prod_update_eq X p k v, prod_update_eq X p' k (p k), prod_update_eq X p' k v,
    ← Finset.mul_prod_erase Finset.univ (fun j => (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (Finset.mem_univ k)]
  ring
end ReciprocityTheory.AnForm.R
