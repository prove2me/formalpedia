-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_eeVd_apply__ec28e3696ecf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:32.96045+00:00
-- url     : https://prove2.me/submissions/58e47cb4-dee7-4be4-8faa-53bbaa4c0d44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (a : Fin n) :
    eeVd E f a = -∑ c, E a c (f c) := by
  simp [eeVd, LinearMap.pi_apply, LinearMap.sum_apply]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
