-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.projQ_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:38.578272+00:00
-- url     : https://prove2.me/submissions/e43e9b1a-d298-4a6d-949c-da08a7be8f12

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
theorem _root_.solution (ℓ : ℂ →ₗ[ℚ] ℚ) (g : MvPolynomial σ ℚ) (h : MvPolynomial σ ℂ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g * h) = g * projQ ℓ h := by
  classical
  ext m
  rw [coeff_projQ, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_projQ]
  have : algebraMap ℚ ℂ (coeff x.1 g) * coeff x.2 h = coeff x.1 g • coeff x.2 h := by
    rw [Algebra.smul_def]
  rw [this, map_smul, smul_eq_mul]
end ReciprocityTheory.AnForm.R
