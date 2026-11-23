-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carU_pOf_add_qOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:48.383005+00:00
-- url     : https://prove2.me/submissions/aa9ff2ca-3bee-4f1e-b7c2-8a97888fe4ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [card_filter, card_filter, ← sum_add_distrib]
  have : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [this]
end ReciprocityTheory.ChartRestriction.DS
