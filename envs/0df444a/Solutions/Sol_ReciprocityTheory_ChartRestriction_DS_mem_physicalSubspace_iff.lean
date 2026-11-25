-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mem_physicalSubspace_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:56.197106+00:00
-- url     : https://prove2.me/submissions/67c60d33-678c-4426-863a-5d27e5e2f188

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited

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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (x : TensorProduct ℂ N (Fock n)) :
    x ∈ physicalSubspace (N := N) ε ↔ ∀ j b, ¬(ε j = true ∧ ε b = false) → cmT j b x = 0 := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
end ReciprocityTheory.ChartRestriction.DS
