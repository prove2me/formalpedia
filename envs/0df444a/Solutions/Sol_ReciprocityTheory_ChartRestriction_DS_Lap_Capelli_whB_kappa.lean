-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:48.173569+00:00
-- url     : https://prove2.me/submissions/7716a976-646c-42c5-9d75-4746b871d94e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_c_val_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_cast_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_g_one

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
theorem _root_.solution (k r : ℕ) (hr : 0 < r) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) :
    kappa k r ψ = (∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))) *
      ((∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) *
        whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))) := by
  have e1 : kappa k r ψ = ∏ n ∈ range (k + 2 * r + 1), whB_g k r ψ (whB_c (k + 2 * r + 1) n) := by
    rw [← Fin.prod_univ_eq_prod_range (fun n => whB_g k r ψ (whB_c (k + 2 * r + 1) n))]
    simp only [whB_c_val_self]; rfl
  rw [e1, show range (k + 2 * r + 1) = range (r + k + r + 1) by congr 1; ring,
    Finset.prod_range_succ, Finset.prod_range_add, Finset.prod_range_add]
  have hW : ∏ x ∈ range k, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + x)) = 1 := by
    refine Finset.prod_eq_one fun x hx => whB_g_one ψ fun b hb => ?_
    rw [Finset.mem_range] at hx
    obtain ⟨_, h2, _⟩ := hb
    exact h2 ⟨by rw [whB_cast_val (by omega)]; omega, by rw [whB_cast_val (by omega)]; omega⟩
  have hL : whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + r)) = 1 := by
    refine whB_g_one ψ fun b hb => ?_
    obtain ⟨h1, _, _⟩ := hb
    have := b.isLt
    simp only [blk, whB_cast_val (show r + k + r < k + 2 * r + 1 by omega)] at h1
    split_ifs at h1 <;> omega
  have hE : ∏ x ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (r + k + x)) =
      ∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [show r + k + x = k + r + x by ring]
  have hS : ∏ n ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (n)) =
      (∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) *
        whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1)) := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, zero_add]
    rw [Finset.prod_range_succ]
  rw [hW, hL, hE, hS]; ring
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
