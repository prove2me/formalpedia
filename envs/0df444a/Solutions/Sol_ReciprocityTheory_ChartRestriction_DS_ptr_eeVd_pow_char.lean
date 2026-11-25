-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ptr_eeVd_pow_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:47.062364+00:00
-- url     : https://prove2.me/submissions/3d5a7027-ea24-40bc-b172-dafea986e6dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coeff_residueSeries_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dualPole_eq_neg_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ptr_eeVd_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeVd E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleVd μ)) • x := by
  rw [ptr_eeVd_pow, LinearMap.smul_apply, (hS k x hx).1, smul_smul, dualPole_eq_neg_shift, coeff_residueSeries_neg]
end ReciprocityTheory.ChartRestriction.DS
