-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ptr_eeVd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:47.109955+00:00
-- url     : https://prove2.me/submissions/a3c6f300-e087-4afc-87a4-59b0ac00e190

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_neg_equiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ptr_eq_gelfand

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeVd E ^ k) = ((-1 : ℂ) ^ k) • gelfand E k := by
  have hA : ∀ f r, eeVd E f r = ∑ s, (fun r s => -E r s) r s (f s) := by
    intro f r
    simp [eeVd, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  simp only [gelfand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ePow_neg_equiv E (Equiv.refl _) k a a
end ReciprocityTheory.ChartRestriction.DS
