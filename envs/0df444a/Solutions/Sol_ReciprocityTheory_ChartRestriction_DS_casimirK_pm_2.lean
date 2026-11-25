-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.casimirK_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:09.120505+00:00
-- url     : https://prove2.me/submissions/f5cc7b86-34c6-4a82-bde0-1f85e3558130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sum_univ_pm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_filter_eq_plus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_filter_eq_minus

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
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by
  unfold casimirK
  rw [csq_sum_univ_pm ε]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_minus ε ha]
end ReciprocityTheory.ChartRestriction.DS
