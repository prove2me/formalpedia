-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.expand_cons_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:43.26806+00:00
-- url     : https://prove2.me/submissions/5cda02e4-fc15-4f26-ab52-453e84061eeb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand

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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {b c : Fin (m + 1)} (h : b ≠ c) :
    ¬ Function.Injective (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) := by
  intro hinj
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h
  have h0 : (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) 0 =
      (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) z.succ := by
    simp [hz]
  exact Fin.succ_ne_zero z (hinj h0).symm
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
