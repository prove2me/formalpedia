-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.exponentCondition_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:56.743783+00:00
-- url     : https://prove2.me/submissions/8ea13b2d-5ff4-40e9-9b55-33b1d17d625e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p : ℕ} (e : Fin (p + 2) → ℝ) {α : ℝ} (he : ∀ l, 0 < e l)
    (hα : 2 * ∑ i : Fin (p + 1), e i.succ < α) :
    CHCond p (Function.update (fun i : Fin (p + 1) => -e i.succ) 0
        (α + (fun i : Fin (p + 1) => -e i.succ) 0)) ∧
      0 < α + 2 * ∑ i, (fun i : Fin (p + 1) => -e i.succ) i := by
  have hpos : ∀ i : Fin (p + 1), 0 ≤ e i.succ := fun i => (he _).le
  have hS : ∀ s : Finset (Fin (p + 1)), ∑ i ∈ s, e i.succ ≤ ∑ i : Fin (p + 1), e i.succ :=
    fun s => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => hpos i
  have hN : ∀ s : Finset (Fin (p + 1)), 0 ≤ ∑ i ∈ s, e i.succ :=
    fun s => Finset.sum_nonneg fun i _ => hpos i
  have hupd : ∀ j, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j = -e j.succ + if j = 0 then α else 0 := by
    intro j
    rw [Function.update_apply]
    split_ifs with hj
    · subst hj
      show α + -e (Fin.succ 0) = -e (Fin.succ 0) + α
      ring
    · show -e j.succ = -e j.succ + 0
      ring
  have hsum : ∀ s : Finset (Fin (p + 1)), ∑ j ∈ s, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j =
        -∑ j ∈ s, e j.succ + if (0 : Fin (p + 1)) ∈ s then α else 0 := by
    intro s
    rw [Finset.sum_congr rfl fun j _ => hupd j, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    congr 1
    simp
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.CHCond
  refine ⟨⟨fun l => ?_, fun l _ => ?_⟩, ?_⟩
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    rw [hsum, if_pos h0]
    linarith [hS (Finset.Iic l), hN Finset.univ]
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    have h0' : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp [Finset.mem_Ioi]
    have hdis : Disjoint (Finset.Iic l) (Finset.Ioi l) :=
      Finset.disjoint_left.2 fun j h1 h2 =>
        lt_irrefl _ (lt_of_le_of_lt (Finset.mem_Iic.1 h1) (Finset.mem_Ioi.1 h2))
    have hAB : ∑ j ∈ Finset.Iic l, e j.succ + ∑ j ∈ Finset.Ioi l, e j.succ ≤
        ∑ j : Fin (p + 1), e j.succ := by
      rw [← Finset.sum_union hdis]; exact hS _
    rw [hsum, hsum, if_pos h0, if_neg h0']
    linarith [hN (Finset.Iic l), hN (Finset.Ioi l)]
  · show 0 < α + 2 * ∑ i : Fin (p + 1), -e i.succ
    rw [Finset.sum_neg_distrib]
    linarith [hN Finset.univ]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
