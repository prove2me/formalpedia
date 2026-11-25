-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:35.660398+00:00
-- url     : https://prove2.me/submissions/9447cfd9-1e01-4abd-be0c-2b4e299bb5dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_neg_one_pow_row
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_neg_one_pow_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_update_row
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_update_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_comm


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i j : Fin (p + 1)) (y : ℂ) :
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        (E (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y -
          cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y * E (R i) (C j)) =
      ∑ t, capT E R C y (i.succAbove t) j - ∑ t, capT E R C y i (j.succAbove t) := by
  rw [cminor_comm (hE := hE) (a := R i) (b := C j) (R := R ∘ i.succAbove)
    (C := C ∘ j.succAbove) (x := y), smul_sub, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    split_ifs with h
    · rw [cminor_update_row, smul_smul, neg_one_pow_row]
    · exact smul_zero _
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    by_cases h : C (j.succAbove t) = R i
    · rw [if_pos h, if_pos h.symm, cminor_update_col E hE, smul_smul, neg_one_pow_col]
    · rw [if_neg h, if_neg (Ne.symm h), smul_zero]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
