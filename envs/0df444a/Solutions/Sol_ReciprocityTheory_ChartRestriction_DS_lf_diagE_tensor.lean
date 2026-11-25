-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_diagE_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:01.702802+00:00
-- url     : https://prove2.me/submissions/8bf585da-5568-44dc-b611-b69409d4f145

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_sgE_tensor

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) :
    diagE ε (eT E) cpT cmT a b =
      TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  unfold diagE
  rw [lf_sgE_tensor]
  rfl
end ReciprocityTheory.ChartRestriction.DS
