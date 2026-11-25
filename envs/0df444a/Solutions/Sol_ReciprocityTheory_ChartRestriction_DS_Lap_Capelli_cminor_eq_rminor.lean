-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_eq_rminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:32.196583+00:00
-- url     : https://prove2.me/submissions/55bec9f3-19e9-473a-b8fe-cdc09d0737b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_comm_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_col_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_comm_term
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_rminor_row_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_sum_sum_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
private theorem eq_of_succ_nsmul_eq_succ_nsmul {M : Type*} [AddCommGroup M] [Module ℂ M] (k : ℕ) {a b : M}
    (h : (k + 1) • a = (k + 1) • b) : a = b := by
  have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have h' : ((k + 1 : ℕ) : ℂ) • a = ((k + 1 : ℕ) : ℂ) • b := by
    rw [Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]; exact h
  calc a = ((k + 1 : ℕ) : ℂ)⁻¹ • (((k + 1 : ℕ) : ℂ) • a) := (inv_smul_smul₀ hne a).symm
    _ = ((k + 1 : ℕ) : ℂ)⁻¹ • (((k + 1 : ℕ) : ℂ) • b) := by rw [h']
    _ = b := inv_smul_smul₀ hne b
private theorem sum_sum_sub_sum_succAbove_eq_zero {M : Type*} [AddCommGroup M] {p : ℕ}
    (T : Fin (p + 1) → Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      (∑ t : Fin p, T (i.succAbove t) j - ∑ t : Fin p, T i (j.succAbove t)) = 0 := by
  simp only [Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T (i.succAbove t) j =
      ∑ j : Fin (p + 1), p • ∑ s, T s j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_sum_succAbove (fun s => T s j))
  have h2 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T i (j.succAbove t) =
      ∑ i : Fin (p + 1), p • ∑ s, T i s :=
    Finset.sum_congr rfl (fun i _ => sum_sum_succAbove (fun s => T i s))
  rw [h1, h2, ← Finset.smul_sum, ← Finset.smul_sum, sub_eq_zero]
  congr 1
  exact Finset.sum_comm
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor E R C x = rminor E R C x := by
  revert R C x
  induction p with
  | zero =>
    intro R C x
    simp [cminor, rminor]
  | succ p ih =>
    intro R C x
    have hcol : ∑ _j : Fin (p + 1), cminor E R C x =
        ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => cminor_col_at E hE R C j x)
    have hrow : ∑ _i : Fin (p + 1), rminor E R C x =
        ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [rminor_row_at E hE R C i x]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ih]
    have hij : ∀ i j : Fin (p + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) -
          ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) =
        ∑ t, capT E R C (x - 1) (i.succAbove t) j -
          ∑ t, capT E R C (x - 1) i (j.succAbove t) := by
      intro i j
      rw [← smul_sub, capEntry_comm_sub]
      exact comm_term E hE R C i j (x - 1)
    have hdiff : ∑ _j : Fin (p + 1), cminor E R C x - ∑ _i : Fin (p + 1), rminor E R C x = 0 := by
      rw [hcol, hrow, ← Finset.sum_sub_distrib]
      simp only [← Finset.sum_sub_distrib, hij]
      have h0 := sum_sum_sub_sum_succAbove_eq_zero (capT E R C (x - 1))
      simp only [Finset.sum_sub_distrib] at h0 ⊢
      exact h0
    have hs := sub_eq_zero.mp hdiff
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hs
    exact eq_of_succ_nsmul_eq_succ_nsmul p hs
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
