-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sum_hwTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:44.103369+00:00
-- url     : https://prove2.me/submissions/f170c002-67f4-41a1-bed7-0890cde37f42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec

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
theorem _root_.solution (S : Fin n → Fin n → Prop) [DecidableRel S] (hrefl : ∀ a, S a a)
    (hS : ∀ a b, S a b → S b a) (μ r : Fin n → ℝ)
    (hr : ∀ a, 2 * r a = ((univ.filter fun b => a < b ∧ S a b).card : ℝ) -
      ((univ.filter fun b => b < a ∧ S a b).card : ℝ)) :
    ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b = nsq (μ + r) - nsq r := by
  classical
  have hpt : ∀ a b, (if S a b then hwTerm μ a b else 0) =
      (if a = b then μ a * μ a else 0) +
        ((if a < b ∧ S a b then μ a else 0) - (if a < b ∧ S a b then μ b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · by_cases hs : S a b <;> simp [hwTerm, h, h.ne, hs]
    · simp [hwTerm, hrefl]
    · by_cases hs : S a b <;> simp [hwTerm, h.ne', not_lt.2 h.le, hs]

  have hL : ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b =
      ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if a < b ∧ S a b then μ b else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    simp only [hpt a, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have hR : nsq (μ + r) - nsq r = ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if b < a ∧ S a b then μ a else 0)) := by
    rw [← Finset.sum_add_distrib]
    unfold nsq dot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : ∑ b, ((if a < b ∧ S a b then μ a else 0) - (if b < a ∧ S a b then μ a else 0)) =
        μ a * (2 * r a) := by
      rw [hr a, Finset.natCast_card_filter, Finset.natCast_card_filter, mul_sub, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [mul_ite, mul_one, mul_zero]
    rw [h2, Pi.add_apply]
    ring
  rw [hL, hR]
  congr 1
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b < a ∧ S a b
  · rw [if_pos h, if_pos ⟨h.1, hS a b h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, hS b a h'.2⟩]
end ReciprocityTheory.ChartRestriction.DS
