-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.l_cminor_lastcol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:44.047899+00:00
-- url     : https://prove2.me/submissions/b1563e2b-ff49-4e19-8903-ab1ee060e9ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_comp_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_l_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_col_at
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
    {p : ℕ} (Rs Cs : Fin (p + 1) → Fin n) (x : ℂ) (hR : ∀ i, bl (Rs i) < bl (Cs (Fin.last p))) :
    l ∘ₗ cminor E Rs Cs x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + p) * ψ (Rs i) (Cs (Fin.last p))) •
      (l ∘ₗ cminor E (Rs ∘ i.succAbove) (Cs ∘ Fin.castSucc) (x - 1)) := by
  rw [cminor_col_at E ((isGlRep_iff_glRelR E).1 hE) Rs Cs (Fin.last p) x, whB_comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_smul, whB_l_entry E bl ψ l hl (hR i), smul_smul, Fin.val_last, Fin.succAbove_last]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
