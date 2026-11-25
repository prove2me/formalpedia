-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.l_cminor_firstrow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:05.402945+00:00
-- url     : https://prove2.me/submissions/bf9cb8d9-38ea-481f-9cf0-5400004e90a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_comp_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_l_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_succ_row
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_isGlRep_iff_glRelR


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
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {p : ℕ} (Rs Cs : Fin (p + 1) → Fin n) (x : ℂ) (hC : ∀ j, bl (Rs 0) < bl (Cs j)) :
    l ∘ₗ cminor E Rs Cs x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ) * ψ (Rs 0) (Cs j)) •
      (l ∘ₗ cminor E (Rs ∘ Fin.succ) (Cs ∘ j.succAbove) x) := by
  rw [cminor_succ_row E ((isGlRep_iff_glRelR E).1 hE) Rs Cs x, whB_comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hC j), smul_smul]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
