-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_tensV_apply__cffaa40c8d7b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:29.2517+00:00
-- url     : https://prove2.me/submissions/b2e61b8c-94b7-422f-baed-d78ee799ead6

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M)
    (e : Fin n) : tensV E a b f e = E a b (f e) + if e = a then f b else 0 := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
