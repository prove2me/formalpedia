-- Prove2me | solution 1 for RevenueOrdered.UDPmin.revenue_ordered_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T04:10:36.223867+00:00
-- url     : https://prove2.me/submissions/f7e372a4-444c-48c1-b011-dc28f3c681f3

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Theorems.Thm_RevenueOrdered_Ratio_revenue_ordered_ratio_bound

open scoped BigOperators
open RevenueOrdered.UDPmin
local notation "IsRegular" => RevenueOrdered.UDPmin.IsRegular
set_option maxHeartbeats 1000000

variable {C : Type*} [Fintype C] [DecidableEq C]

private lemma ur_level (r : C → ℝ) (i : Fin (numRev r)) :
    RevenueOrdered.Ratio.level r (i.val+1) = revAt r i := by
  unfold RevenueOrdered.Ratio.level
  rw [dif_pos (by change 1 ≤ i.val+1 ∧ i.val+1 ≤ numRev r; omega)]
  simp only [Nat.add_sub_cancel]
  rfl

private lemma ur_prev (r : C → ℝ) (i : Fin (numRev r)) :
    RevenueOrdered.Ratio.level r i.val = prevRev r i := by
  unfold prevRev RevenueOrdered.Ratio.level
  by_cases h : i.val=0
  · simp [h]
  · rw [dif_neg h, dif_pos (by change 1 ≤ i.val ∧ i.val ≤ numRev r; omega)]
    rfl

private lemma ur_sum (r : C → ℝ) : ratioSum r = RevenueOrdered.Ratio.ratioSum r := by
  classical
  unfold ratioSum RevenueOrdered.Ratio.ratioSum
  apply Finset.sum_bij (fun (i : Fin (numRev r)) _ => i.val+1)
  · intro i hi
    rw [Finset.mem_Icc]
    change 1 ≤ i.val+1 ∧ i.val+1 ≤ numRev r
    omega
  · intro i hi j hj h
    apply Fin.ext
    omega
  · intro n hn
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hn
    change n ≤ numRev r at h2
    refine ⟨⟨n-1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [Fin.val_mk]
    omega
  · intro i hi
    rw [ur_level, Nat.add_sub_cancel, ur_prev]

private lemma ur_ro [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ) :
    ro P r = RevenueOrdered.Ratio.roValue P r := by
  classical
  apply le_antisymm
  · unfold ro
    apply Finset.sup'_le
    intro t ht
    have ht' : t ∈ Set.range (revAt r) := by
      let e := (revValues r).orderIsoOfFin (k := numRev r) rfl
      refine ⟨e.symm ⟨t, ht⟩, ?_⟩
      exact congrArg (fun q : {x // x ∈ revValues r} => q.val) (e.apply_symm_apply ⟨t, ht⟩)
    obtain ⟨j, rfl⟩ := ht'
    have hm : j.val+1 ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r) := by
      rw [Finset.mem_Icc]
      change 1 ≤ j.val+1 ∧ j.val+1 ≤ numRev r
      omega
    have hh := Finset.le_sup' (fun k => RevenueOrdered.Ratio.revenue P r
      (RevenueOrdered.Ratio.roSet r k)) hm
    change RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r (j.val+1)) ≤
      RevenueOrdered.Ratio.roValue P r at hh
    simpa only [RevenueOrdered.Ratio.roSet, ur_level, RevenueOrdered.Ratio.revenue,
      RevenueOrdered.Tightness.rev, thresholdSet] using hh
  · unfold RevenueOrdered.Ratio.roValue
    apply Finset.sup'_le
    intro k hk
    obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hk
    have hm : RevenueOrdered.Ratio.level r k ∈ revValues r := by
      unfold RevenueOrdered.Ratio.level
      rw [dif_pos ⟨h1,h2⟩]
      exact Finset.orderEmbOfFin_mem _ rfl _
    have hh := Finset.le_sup' (fun t => RevenueOrdered.Tightness.rev P r (thresholdSet r t)) hm
    change RevenueOrdered.Tightness.rev P r (thresholdSet r (RevenueOrdered.Ratio.level r k)) ≤ ro P r at hh
    exact hh

private lemma ur_extrema [Nonempty C] (r : C → ℝ) :
    RevenueOrdered.Ratio.level r (RevenueOrdered.Ratio.numVals r) = rMax r ∧
      RevenueOrdered.Ratio.level r 1 = rMin r := by
  have hn := RevenueOrdered.Ratio.numVals_pos r
  constructor
  · unfold RevenueOrdered.Ratio.level
    rw [dif_pos ⟨hn, le_rfl⟩]
    exact Finset.orderEmbOfFin_last rfl hn
  · unfold RevenueOrdered.Ratio.level
    rw [dif_pos ⟨le_rfl, hn⟩]
    exact Finset.orderEmbOfFin_zero rfl hn

theorem solution {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    RevenueOrdered.Ratio.opt P r ≤ ratioSum r * ro P r ∧
    ratioSum r ≤ 1 + Real.log (rMax r / rMin r) := by
  have hp : RevenueOrdered.Ratio.IsRegular P :=
    ⟨hP.nonneg, hP.noPurchase_nonneg, hP.eq_zero_of_not_mem, hP.sum_le_one,
      hP.antitone, hP.noPurchase_antitone⟩
  have h := RevenueOrdered.Ratio.revenue_ordered_ratio_bound P hp r hr
  rw [← ur_sum, ← ur_ro, (ur_extrema r).1, (ur_extrema r).2] at h
  exact h

#print axioms solution
