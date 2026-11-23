-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.prod_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:34.688259+00:00
-- url     : https://prove2.me/submissions/d262bcd8-0eed-424c-ae64-e6b71b1dc6bd

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

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
    (p : (k : K) → ι k) (k : K) (v : ι k) :
    ∏ j, x ⟨j, Function.update p k v j⟩ = x ⟨k, v⟩ * ∏ j ∈ Finset.univ.erase k, x ⟨j, p j⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
end ReciprocityTheory.AnForm.R
