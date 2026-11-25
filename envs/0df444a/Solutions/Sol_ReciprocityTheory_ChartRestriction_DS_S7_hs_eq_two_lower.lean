-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_eq_two_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:22.185026+00:00
-- url     : https://prove2.me/submissions/d7a450a5-af9e-4065-84d1-d446d678abbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_entry_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inP_norm_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    hs Y = 2 * ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
  have hsplit : ∀ a b : Fin n, ‖Y a b‖ ^ 2 =
      (if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [inP_entry_zero hY rfl]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [inP_norm_symm hY]
  unfold hs
  calc (∑ a : Fin n, ∑ b : Fin n, ‖Y a b‖ ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, ((if b < a then ‖Y a b‖ ^ 2 else 0) + (if a < b then ‖Y a b‖ ^ 2 else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = (∑ a : Fin n, ∑ b : Fin n, if b < a then ‖Y a b‖ ^ 2 else 0) +
        ∑ a : Fin n, ∑ b : Fin n, if a < b then ‖Y a b‖ ^ 2 else 0 := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring
end ReciprocityTheory.ChartRestriction.DS.S7
