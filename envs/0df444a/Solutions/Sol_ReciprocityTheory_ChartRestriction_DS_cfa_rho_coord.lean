-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.cfa_rho_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:40.575709+00:00
-- url     : https://prove2.me/submissions/e1c164fb-0c6d-490f-8c21-0483c979fb69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = ∑ b, ((if ε c = true ∧ ε b = false ∧ b < c then (1 : ℝ) else 0) -
      (if ε b = true ∧ ε c = false ∧ c < b then (1 : ℝ) else 0)) := by
  have e1 : ∀ (p : Fin n → Prop) [DecidablePred p],
      (((univ.filter p).card : ℕ) : ℝ) = ∑ b, if p b then (1 : ℝ) else 0 := by
    intro p _
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [Pi.sub_apply, rhoHol, rhoN, qOf, pOf]
  rw [e1, e1, e1, e1]
  cases hc : ε c
  · simp only [Bool.false_eq_true, if_false, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b c with h | h | h
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
    · subst h; simp [hc]
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
  · simp only [if_true, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b c with h | h | h
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
    · subst h; simp [hc]
    · cases hb : ε b <;> simp [hb, hc, h, lt_asymm h, h.ne, h.ne'] <;> norm_num
end ReciprocityTheory.ChartRestriction.DS
