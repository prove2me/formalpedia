-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.segreW_prod_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:19.941497+00:00
-- url     : https://prove2.me/submissions/16c21787-e29b-4f33-9b0a-814d42ac6170

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Theorems.Thm_ReciprocityTheory_AnForm_R_prod_prod_update
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
    (p p' : (k : K) → ι k) :
    (∏ k, segreW P (Function.update p k (p' k))) * segreW P p =
      segreW P p' * segreW P p ^ Fintype.card K := by
  simp only [segreW, ← map_prod, ← map_mul, ← map_pow]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, map_prod, map_pow, segreMap_X]
  exact prod_prod_update (X : (Σ k, ι k) → MvPolynomial (Σ k, ι k) ℂ) p p'
end ReciprocityTheory.AnForm.R
