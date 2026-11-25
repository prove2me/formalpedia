-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_expand_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:03.433683+00:00
-- url     : https://prove2.me/submissions/134261b2-0614-4d33-9a70-13ec87f34d7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_expand_cons_succAbove_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_expand_sign_cycleRange_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_expand_cons_not_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_cols_not_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_cols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_succ_col


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
theorem _root_.solution (hE : GlRelR E) (om : ℂ) (b c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      if b = c then capelliC E om else 0 := by
  have key : cminor E id (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) om =
      ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) := by
    rw [cminor_succ_col]
    rfl
  have hsum : ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      ((-1 : ℂ) ^ (c : ℕ)) • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, pow_add, mul_comm]
  rw [hsum, ← key]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl, expand_cons_succAbove_eq, cminor_perm_cols (E := E) hE,
      ← Int.cast_smul_eq_zsmul ℂ, expand_sign_cycleRange_symm, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_smul]
    rfl
  · rw [if_neg hbc, cminor_cols_not_inj (E := E) hE _ _ _ (expand_cons_not_inj hbc), smul_zero]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
