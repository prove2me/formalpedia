-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.coeff_projQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:47.319749+00:00
-- url     : https://prove2.me/submissions/41304f3d-5e21-4b01-b8de-79e66350af9a

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract

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
theorem _root_.solution (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (projQ ℓ q) = ℓ (coeff m q) := by
  classical
  rw [projQ, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, map_zero]
end ReciprocityTheory.AnForm.R
