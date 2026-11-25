-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_mem_phys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:33.697909+00:00
-- url     : https://prove2.me/submissions/6743040e-d91f-41eb-ac57-062f2fd7a175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (i a : Fin n) :
    finProdFinEquiv (i, a) ∈ lfPhysModes ε ↔ ε i = true ∧ ε a = false := by
  simp only [lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
end ReciprocityTheory.ChartRestriction.DS
