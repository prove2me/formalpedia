-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fock_inv_cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:04.07936+00:00
-- url     : https://prove2.me/submissions/7b0d5212-f9ba-4acf-9be2-331214ff8440

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA

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
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cpFock, CliffordAlgebra.involute_ι]
end ReciprocityTheory.ChartRestriction.DS
