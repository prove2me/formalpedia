-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fock_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:37.828621+00:00
-- url     : https://prove2.me/submissions/a4fa3de2-8585-487e-bd4f-a6fbf75db4f0

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
theorem _root_.solution :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 :=
  LinearMap.ext fun x => CliffordAlgebra.involute_involute x
end ReciprocityTheory.ChartRestriction.DS
