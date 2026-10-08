-- Prove2me | solution 1 for RevenueOrdered.Ratio.revenue_le_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:49:08.058981+00:00
-- url     : https://prove2.me/submissions/47296b6c-6b3c-4310-b31a-3df7f00ddad0

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

set_option autoImplicit false

namespace RevenueOrdered.Ratio.WSumAux

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

end RevenueOrdered.Ratio.WSumAux

open RevenueOrdered.Ratio in
theorem layer_sum {C : Type*} [Fintype C] [DecidableEq C]
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
        rw [RevenueOrdered.Ratio.WSumAux.key r x]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        split_ifs <;> ring

open RevenueOrdered.Ratio in
theorem layer_ineq {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (Sstar : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ numVals r) :
    ∑ x ∈ Sstar ∩ roSet r i, P x Sstar * level r i ≤ revenue P r (roSet r i) := by
  set T := Sstar ∩ roSet r i with hT
  set S := roSet r i with hS
  have hTS : T ⊆ S := Finset.inter_subset_right
  have hTstar : T ⊆ Sstar := Finset.inter_subset_left
  -- level is nonneg? not needed: use r_i ≤ r x on S and positivity of r
  have hlev : ∀ x ∈ S, level r i ≤ r x := by
    intro x hx
    simpa [hS, roSet] using hx
  -- level r i is positive: it is a value of r (or 0); we only need 0 ≤ level r i
  have hlev0 : 0 ≤ level r i := by
    unfold level
    split_ifs with h
    · have hmem : sortedVals r ⟨i - 1, by omega⟩ ∈ revVals r := by
        unfold sortedVals
        exact Finset.orderEmbOfFin_mem _ _ _
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
      rw [← hx]; exact (hr x).le
    · exact le_rfl
  -- step 1: P x Sstar ≤ P x T for x ∈ T
  have h1 : ∑ x ∈ T, P x Sstar * level r i ≤ ∑ x ∈ T, P x T * level r i := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_right (hP.mono T Sstar x hTstar hx) hlev0
  -- step 2: purchase probability monotone
  have h2 : ∑ x ∈ T, P x T ≤ ∑ x ∈ S, P x S := by
    have := hP.noPurchase_mono T S hTS
    unfold noPurchase at this
    linarith
  -- step 3: level ≤ r on S
  have h3 : ∑ x ∈ S, P x S * level r i ≤ ∑ x ∈ S, P x S * r x := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (hlev x hx) (hP.nonneg x S)
  calc ∑ x ∈ T, P x Sstar * level r i ≤ ∑ x ∈ T, P x T * level r i := h1
    _ = (∑ x ∈ T, P x T) * level r i := by rw [Finset.sum_mul]
    _ ≤ (∑ x ∈ S, P x S) * level r i := mul_le_mul_of_nonneg_right h2 hlev0
    _ = ∑ x ∈ S, P x S * level r i := by rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ S, P x S * r x := h3
    _ = revenue P r S := rfl

open RevenueOrdered.Ratio in
theorem RevenueOrdered.Ratio.WSumAux.level_pos {C : Type*} [Fintype C] (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ numVals r) : 0 < level r l := by
  rw [RevenueOrdered.Ratio.WSumAux.level_eq r l h1 h2]
  have hmem : sortedVals r ⟨l - 1, by omega⟩ ∈ revVals r := by
    unfold sortedVals
    exact Finset.orderEmbOfFin_mem _ _ _
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
  rw [← hx]; exact hr x

open RevenueOrdered.Ratio in
theorem RevenueOrdered.Ratio.WSumAux.level_mono {C : Type*} [Fintype C] (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ numVals r) : level r (l - 1) ≤ level r l := by
  rcases Nat.lt_or_ge l 2 with h | h
  · have : l - 1 = 0 := by omega
    rw [this, RevenueOrdered.Ratio.WSumAux.level_zero]
    exact (RevenueOrdered.Ratio.WSumAux.level_pos r hr l h1 h2).le
  · rw [RevenueOrdered.Ratio.WSumAux.level_eq r l h1 h2,
      RevenueOrdered.Ratio.WSumAux.level_eq r (l - 1) (by omega) (by omega)]
    apply (sortedVals r).monotone
    rw [Fin.le_def]
    simp only
    omega

open RevenueOrdered.Ratio in
theorem solution {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (Sstar : Finset C) :
    revenue P r Sstar ≤
      ∑ l ∈ Finset.Icc 1 (numVals r),
        (level r l - level r (l - 1)) / level r l * revenue P r (roSet r l) := by
  rw [layer_sum P r hr Sstar]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mem_Icc] at hl
  have hpos := RevenueOrdered.Ratio.WSumAux.level_pos r hr l hl.1 hl.2
  have hd : 0 ≤ level r l - level r (l - 1) :=
    sub_nonneg.mpr (RevenueOrdered.Ratio.WSumAux.level_mono r hr l hl.1 hl.2)
  have hi := layer_ineq P hP r hr Sstar l hl.1 hl.2
  rw [← Finset.sum_mul] at hi
  have hs : ∑ x ∈ Sstar ∩ roSet r l, P x Sstar ≤ revenue P r (roSet r l) / level r l := by
    rw [le_div_iff₀ hpos]; exact hi
  calc (level r l - level r (l - 1)) * ∑ x ∈ Sstar ∩ roSet r l, P x Sstar
      ≤ (level r l - level r (l - 1)) * (revenue P r (roSet r l) / level r l) :=
        mul_le_mul_of_nonneg_left hs hd
    _ = (level r l - level r (l - 1)) / level r l * revenue P r (roSet r l) := by ring
