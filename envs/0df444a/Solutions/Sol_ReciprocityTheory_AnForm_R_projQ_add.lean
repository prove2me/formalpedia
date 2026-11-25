-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.projQ_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:37.220658+00:00
-- url     : https://prove2.me/submissions/a35345e7-ecd5-4b11-8785-ed94554180f0

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Theorems.Thm_ReciprocityTheory_AnForm_R_coeff_projQ

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
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (ℓ : ℂ →ₗ[ℚ] ℚ) (a b : MvPolynomial σ ℂ) :
    projQ ℓ (a + b) = projQ ℓ a + projQ ℓ b := by
  ext m
  simp [coeff_projQ]
end ReciprocityTheory.AnForm.R
