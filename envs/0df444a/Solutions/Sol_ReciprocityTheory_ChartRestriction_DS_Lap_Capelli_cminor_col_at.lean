-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_col_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:13.51184+00:00
-- url     : https://prove2.me/submissions/79c77943-58f6-4b01-b827-651bbc2753e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_cols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_succ_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_permIns_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_permIns_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_sign_permIns


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
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin (p + 1)) (x : ℂ) :
    cminor E R C x = ∑ i : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by
  have hπ := cminor_perm_cols E hE R C (permIns j 1) x
  rw [sign_permIns, Equiv.Perm.sign_one, Units.val_one, mul_one] at hπ
  have h0 := cminor_succ_col E R (C ∘ permIns j 1) x
  have hC0 : (C ∘ permIns j 1) 0 = C j := by rw [Function.comp_apply, permIns_zero]
  have hCs : (C ∘ permIns j 1) ∘ Fin.succ = C ∘ j.succAbove := by
    funext m
    simp only [Function.comp_apply, permIns_succ, Equiv.Perm.one_apply]
  rw [hC0, hCs, hπ] at h0
  have hsq : cminor E R C x =
      ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (j : ℕ)) • cminor E R C x) := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [hsq, h0, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
