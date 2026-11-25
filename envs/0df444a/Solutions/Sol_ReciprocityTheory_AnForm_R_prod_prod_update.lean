-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.prod_prod_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:24.459208+00:00
-- url     : https://prove2.me/submissions/cd82e62c-1872-491c-b852-bf68c283625f

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_update_eq

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
theorem _root_.solution {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p p' : (k : K) → ι k) :
    (∏ k, ∏ j, x ⟨j, Function.update p k (p' k) j⟩) * ∏ j, x ⟨j, p j⟩ =
      (∏ k, x ⟨k, p' k⟩) * (∏ j, x ⟨j, p j⟩) ^ Fintype.card K := by
  simp_rw [prod_update_eq x p]
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul Finset.univ (fun j => x ⟨j, p j⟩)
    (Finset.mem_univ k)]
  rw [Finset.prod_const, Finset.card_univ]
end ReciprocityTheory.AnForm.R
