-- Prove2me | solution 1 for RevenueOrdered.Ratio.revenue_eq_layer_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:24:18.772839+00:00
-- url     : https://prove2.me/submissions/03ef9ee3-55ce-4d41-a822-a2f5bf1231b4

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

set_option autoImplicit false

namespace RevenueOrdered.Ratio.LayerSumAux

lemma telescope (f : ℕ → ℝ) : ∀ m : ℕ,
    ∑ l ∈ Finset.Icc 1 m, (f l - f (l - 1)) = f m - f 0
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), telescope f m]
    simp

lemma level_zero {C : Type*} [Fintype C] (r : C → ℝ) :
    RevenueOrdered.Ratio.level r 0 = 0 := by
  simp [RevenueOrdered.Ratio.level]

lemma level_eq {C : Type*} [Fintype C] (r : C → ℝ) (l : ℕ) (h1 : 1 ≤ l)
    (h2 : l ≤ RevenueOrdered.Ratio.numVals r) :
    RevenueOrdered.Ratio.level r l =
      RevenueOrdered.Ratio.sortedVals r ⟨l - 1, by omega⟩ := by
  simp [RevenueOrdered.Ratio.level, h1, h2]

lemma key {C : Type*} [Fintype C] (r : C → ℝ) (x : C) :
    ∑ l ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r),
      (if RevenueOrdered.Ratio.level r l ≤ r x then
        RevenueOrdered.Ratio.level r l - RevenueOrdered.Ratio.level r (l - 1) else 0) = r x := by
  have hmem : r x ∈ RevenueOrdered.Ratio.revVals r := by
    simp [RevenueOrdered.Ratio.revVals]
  have hrange : r x ∈ Set.range (RevenueOrdered.Ratio.sortedVals r) := by
    have hr := Finset.range_orderEmbOfFin (RevenueOrdered.Ratio.revVals r)
      (rfl : (RevenueOrdered.Ratio.revVals r).card = RevenueOrdered.Ratio.numVals r)
    have hmem' : r x ∈ ((RevenueOrdered.Ratio.revVals r : Finset ℝ) : Set ℝ) :=
      Finset.mem_coe.mpr hmem
    rw [← hr] at hmem'
    exact hmem'
  obtain ⟨j, hj⟩ := hrange
  have hjk : j.val + 1 ≤ RevenueOrdered.Ratio.numVals r := j.isLt
  have hiff : ∀ l ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r),
      (RevenueOrdered.Ratio.level r l ≤ r x ↔ l ≤ j.val + 1) := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [level_eq r l hl.1 hl.2, ← hj, OrderEmbedding.le_iff_le, Fin.le_def]
    simp only
    omega
  rw [Finset.sum_congr rfl (fun l hl => by rw [if_congr (hiff l hl) rfl rfl])]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 (RevenueOrdered.Ratio.numVals r)).filter (fun l => l ≤ j.val + 1)
      = Finset.Icc 1 (j.val + 1) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt, telescope, level_zero, level_eq r (j.val + 1) (by omega) hjk, ← hj]
  simp

end RevenueOrdered.Ratio.LayerSumAux

open RevenueOrdered.Ratio in
theorem solution {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (hr : ∀ x, 0 < r x) (Sstar : Finset C) :
    revenue P r Sstar =
      ∑ l ∈ Finset.Icc 1 (numVals r),
        (level r l - level r (l - 1)) * ∑ x ∈ Sstar ∩ roSet r l, P x Sstar := by
  have h1 : ∀ l, ∑ x ∈ Sstar ∩ roSet r l, P x Sstar =
      ∑ x ∈ Sstar, if level r l ≤ r x then P x Sstar else 0 := by
    intro l
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [roSet]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold revenue
  refine Finset.sum_congr rfl (fun x _ => ?_)
  calc P x Sstar * r x
      = P x Sstar * ∑ l ∈ Finset.Icc 1 (numVals r),
          (if level r l ≤ r x then level r l - level r (l - 1) else 0) := by
        rw [RevenueOrdered.Ratio.LayerSumAux.key r x]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        split_ifs <;> ring
