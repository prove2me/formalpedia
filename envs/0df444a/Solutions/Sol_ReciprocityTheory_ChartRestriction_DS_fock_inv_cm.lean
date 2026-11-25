-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fock_inv_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:48.039025+00:00
-- url     : https://prove2.me/submissions/890315c8-7cc9-4f09-a5af-6791baba4cc7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_contractLeft_involute

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
theorem _root_.solution (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cmFock i a =
      -(cmFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cmFock, fock_contractLeft_involute]
end ReciprocityTheory.ChartRestriction.DS
