-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lam_hol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:38.316945+00:00
-- url     : https://prove2.me/submissions/4b06487f-6240-4146-aeb5-1c7c44a29412

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_card_filter_fin

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
theorem _root_.solution (p q : ℕ) (a b : ℤ) (i : Fin (p + q)) :
    (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) i =
      if (i : ℕ) < p then (a : ℝ) - q / 2 + ((p : ℝ) - 1) / 2 - (i : ℕ)
      else (b : ℝ) + p / 2 + ((q : ℝ) - 1) / 2 - (((i : ℕ) : ℝ) - p) := by
  have hi := i.2
  simp only [Pi.add_apply, Pi.sub_apply, rhoN, rhoC, detWt]
  by_cases h : (i : ℕ) < p
  · have r1 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = (q : ℝ) := by
      rw [card_filter_fin _ (p) (p + q) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r2 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = 0 := by
      rw [card_filter_fin _ (0) (0) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r3 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) - (i : ℕ) - 1 := by
      rw [card_filter_fin _ ((i : ℕ) + 1) (p) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r4 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = ((i : ℕ) : ℝ) := by
      rw [card_filter_fin _ (0) ((i : ℕ)) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    rw [if_pos h, if_pos h, r1, r2, r3, r4]
    ring
  · have r1 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = 0 := by
      rw [card_filter_fin _ (0) (0) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r2 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b ≠ epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) := by
      rw [card_filter_fin _ (0) (p) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r3 : (((univ.filter fun b : Fin (p + q) => i < b ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = (p : ℝ) + q - (i : ℕ) - 1 := by
      rw [card_filter_fin _ ((i : ℕ) + 1) (p + q) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    have r4 : (((univ.filter fun b : Fin (p + q) => b < i ∧ epsHol p q b = epsHol p q i).card : ℕ) : ℝ) = ((i : ℕ) : ℝ) - p := by
      rw [card_filter_fin _ (p) ((i : ℕ)) (by omega) fun b => by
          have := b.2
          simp only [epsHol, Fin.lt_def, ne_eq, decide_eq_decide]
          omega,
        Nat.cast_sub (by omega)]
      all_goals (try push_cast)
      all_goals (try ring)
    rw [if_neg h, if_neg h, r1, r2, r3, r4]
    ring
end ReciprocityTheory.ChartRestriction.DS.S7
