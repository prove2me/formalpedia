-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_cols_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:17.786058+00:00
-- url     : https://prove2.me/submissions/739e008d-ce24-4d3c-b7b7-a6e2420c05dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_cols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_eq_zero_of_eq_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_swap_of_not_inj


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ)
    (h : ¬ Function.Injective C) : cminor E R C x = 0 := by
  obtain ⟨i, k, hik, hC⟩ := basic_swap_of_not_inj C h
  apply basic_eq_zero_of_eq_neg
  have := cminor_perm_cols E hE R C (Equiv.swap i k) x
  rw [hC, Equiv.Perm.sign_swap hik] at this
  exact this
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
