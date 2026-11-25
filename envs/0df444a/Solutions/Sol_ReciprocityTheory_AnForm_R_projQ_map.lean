-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.projQ_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:24.819063+00:00
-- url     : https://prove2.me/submissions/7724a6be-af09-4c73-bb72-9983592f86ac

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
theorem _root_.solution (ℓ : ℂ →ₗ[ℚ] ℚ) (hℓ : ℓ 1 = 1) (g : MvPolynomial σ ℚ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g) = g := by
  ext m
  rw [coeff_projQ, coeff_map]
  have : algebraMap ℚ ℂ (coeff m g) = coeff m g • (1 : ℂ) := by
    rw [Algebra.smul_def, mul_one]
  rw [this, map_smul, hℓ, smul_eq_mul, mul_one]
end ReciprocityTheory.AnForm.R
