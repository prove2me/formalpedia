-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfLift_mem_tensFock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:26.415243+00:00
-- url     : https://prove2.me/submissions/be7517f2-5004-497e-b05d-7cc78114f38b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE

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
theorem _root_.solution (ε : Fin n → Bool) {V : Submodule ℂ N} {x : LfIdx ε → N} (hx : ∀ S, x S ∈ V) :
    lfLift ε x ∈ tensFock (n := n) V := by
  unfold lfLift tensFock
  refine Submodule.sum_mem _ fun S _ => ⟨⟨x S, hx S⟩ ⊗ₜ fockBasis n S.1, ?_⟩
  simp [TensorProduct.map_tmul]
end ReciprocityTheory.ChartRestriction.DS
