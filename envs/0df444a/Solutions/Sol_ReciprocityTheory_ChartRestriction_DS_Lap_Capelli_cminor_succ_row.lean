-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_succ_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:13.476175+00:00
-- url     : https://prove2.me/submissions/d5fa2093-00f0-4029-babf-ab2e67691652

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_eq_rminor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_rminor_succ_row


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    cminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      (capEntry E (x - (p : ℂ)) (R 0) (C j) * cminor E (R ∘ Fin.succ) (C ∘ j.succAbove) x) := by
  rw [cminor_eq_rminor E hE, rminor_succ_row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cminor_eq_rminor E hE]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
