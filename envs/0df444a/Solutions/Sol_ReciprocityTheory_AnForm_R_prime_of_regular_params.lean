-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.prime_of_regular_params
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:34.772102+00:00
-- url     : https://prove2.me/submissions/fbd2bc6b-73e7-4ce9-9f7f-58a0c135de35

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_not_mem_sq
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (i : Fin n) : Prime (f i) := by
  have hm : f i ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact prime_of_not_mem_sq hm ((regular_params_spec f hspan hdim).1 i)
end ReciprocityTheory.AnForm.R
