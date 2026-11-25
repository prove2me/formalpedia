-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mem_lowerWedge_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:42.024446+00:00
-- url     : https://prove2.me/submissions/fc4ec7ed-27b2-4abe-9557-d87973fc157f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockC

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
theorem _root_.solution (ε : Fin n → Bool) (x : Fin n × Fin n) :
    finProdFinEquiv x ∈ (lowerWedgeAlt ε).1 ↔ ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := by
  simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    and_assoc]
end ReciprocityTheory.ChartRestriction.DS
