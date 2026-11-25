-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfLift_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:28.077468+00:00
-- url     : https://prove2.me/submissions/e3cad002-bc37-4039-b387-9558befc875c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfLift_tcoef

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
theorem _root_.solution (ε : Fin n → Bool) {x : LfIdx ε → N} (hx : x ≠ 0) : lfLift ε x ≠ 0 := by
  intro h0
  apply hx
  funext S
  have h1 := lfLift_tcoef ε x S
  rw [h0, map_zero] at h1
  exact h1.symm
end ReciprocityTheory.ChartRestriction.DS
