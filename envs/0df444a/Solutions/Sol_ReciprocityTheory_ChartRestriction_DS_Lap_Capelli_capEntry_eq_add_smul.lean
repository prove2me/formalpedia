-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_eq_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:17.505236+00:00
-- url     : https://prove2.me/submissions/196ae2ea-6d40-492e-8c68-f7f3855b4cad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti

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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (x : ℂ) (a b : Fin n) :
    capEntry E x a b = E a b + (if a = b then x else 0) • (1 : 𝒰) := by
  unfold capEntry
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
