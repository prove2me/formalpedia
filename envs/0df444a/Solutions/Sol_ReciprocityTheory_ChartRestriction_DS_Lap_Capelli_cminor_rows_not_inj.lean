-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_rows_not_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:39.14081+00:00
-- url     : https://prove2.me/submissions/0f3d9b56-43cc-40d9-965f-5e67b046896a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_eq_zero_of_eq_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_swap_of_not_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_rows

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
theorem _root_.solution {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) (h : ¬ Function.Injective R) :
    cminor E R C x = 0 := by
  obtain ⟨i, j, hij, hR⟩ := basic_swap_of_not_inj R h
  have h1 := cminor_perm_rows E R C (Equiv.swap i j) x
  rw [hR, Equiv.Perm.sign_swap hij] at h1
  exact basic_eq_zero_of_eq_neg _ h1
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
