-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_perm_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:50.801055+00:00
-- url     : https://prove2.me/submissions/6db15b98-3327-447c-a74b-0e0b4d2b58c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_permIns_bijective

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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {M : Type*} [AddCommMonoid M] {p : ℕ} (F : Equiv.Perm (Fin (p + 1)) → M) :
    ∑ σ, F σ = ∑ i, ∑ τ, F (permIns i τ) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (permIns_bijective (p := p))) F, Fintype.sum_prod_type]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
