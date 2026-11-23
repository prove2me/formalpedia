-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eT_commutesCAR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:58.143333+00:00
-- url     : https://prove2.me/submissions/83276e60-88ea-4824-b1c1-cb4cd7b515e0

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ N) : CommutesCAR (eT E) cpT cmT := by
  intro a b i j
  refine ⟨TensorProduct.ext' fun x y => ?_, TensorProduct.ext' fun x y => ?_⟩ <;>
    simp [eT, cpT, cmT, TensorProduct.map_tmul]
end ReciprocityTheory.ChartRestriction.DS
