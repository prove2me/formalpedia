-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_filter_eq_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:36.530844+00:00
-- url     : https://prove2.me/submissions/814338c3-6cc2-49fe-a51e-bfaee60bb3c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA

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
theorem _root_.solution (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    univ.filter (fun b => ε b = ε a) = minusIdx ε := by
  have h : ε a = false := by simpa [minusIdx] using ha
  ext b
  simp [minusIdx, h]
end ReciprocityTheory.ChartRestriction.DS
