-- Prove2me | solution 1 for RevenueOrdered.PurchaseRatio.revenue_ordered_purchase_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:58:59.778405+00:00
-- url     : https://prove2.me/submissions/9cbb6f6c-c288-4cc2-96ce-203b75c26bbb

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

set_option autoImplicit false

namespace FD2F4BF9Aux

lemma abel (f g : ℕ → ℝ) : ∀ m : ℕ,
    ∑ l ∈ Finset.Icc 1 m, (f l - f (l - 1)) * g l =
      ∑ l ∈ Finset.Icc 1 m, f l * (g l - g (l + 1)) + f m * g (m + 1) - f 0 * g 1
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), abel f g m]
    simp only [Nat.add_sub_cancel]
    ring

lemma log_sum (a : ℕ → ℝ) : ∀ m : ℕ, 1 ≤ m → (∀ i, 1 ≤ i → i ≤ m → 0 < a i) →
    ∑ i ∈ Finset.Ico 1 m, (a i - a (i + 1)) / a i ≤ Real.log (a 1 / a m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro h
    have h1 := h 1 le_rfl le_rfl
    simp [div_self (ne_of_gt h1)]
  | succ m hm ih =>
    intro hpos
    have h' := ih (fun i h1 h2 => hpos i h1 (by omega))
    rw [Finset.sum_Ico_succ_top hm]
    have ham : 0 < a m := hpos m hm (by omega)
    have ham1 : 0 < a (m + 1) := hpos (m + 1) (by omega) le_rfl
    have ha1 : 0 < a 1 := hpos 1 le_rfl (by omega)
    have hx : 0 < a m / a (m + 1) := div_pos ham ham1
    have hlog := Real.one_sub_inv_le_log_of_pos hx
    have hsplit : Real.log (a 1 / a (m + 1))
        = Real.log (a 1 / a m) + Real.log (a m / a (m + 1)) := by
      rw [← Real.log_mul (ne_of_gt (div_pos ha1 ham)) (ne_of_gt hx)]
      congr 1
      field_simp
    have hterm : (a m - a (m + 1)) / a m = 1 - (a m / a (m + 1))⁻¹ := by
      rw [inv_div]
      field_simp
    rw [hterm, hsplit]
    linarith

lemma level_zero {C : Type*} [Fintype C] (r : C → ℝ) :
    RevenueOrdered.Ratio.level r 0 = 0 := by
  simp [RevenueOrdered.Ratio.level]

lemma level_mono {C : Type*} [Fintype C] (r : C → ℝ) (i : ℕ) (hi : 1 ≤ i)
    (hik : i + 1 ≤ RevenueOrdered.Ratio.numVals r) :
    RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.level r (i + 1) := by
  unfold RevenueOrdered.Ratio.level
  rw [dif_pos ⟨hi, by omega⟩, dif_pos ⟨by omega, hik⟩]
  rw [OrderEmbedding.le_iff_le, Fin.le_def]
  simp only
  omega

lemma level_nonneg {C : Type*} [Fintype C] (r : C → ℝ) (hr : ∀ x, 0 < r x) (i : ℕ) :
    0 ≤ RevenueOrdered.Ratio.level r i := by
  unfold RevenueOrdered.Ratio.level
  split_ifs with h
  · have hmem : RevenueOrdered.Ratio.sortedVals r ⟨i - 1, by omega⟩ ∈
        RevenueOrdered.Ratio.revVals r := by
      unfold RevenueOrdered.Ratio.sortedVals
      exact Finset.orderEmbOfFin_mem _ _ _
    unfold RevenueOrdered.Ratio.revVals at hmem
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
    rw [← hx]
    exact (hr x).le
  · exact le_rfl

open RevenueOrdered.PurchaseRatio in
lemma N_nonneg {C : Type*} [Fintype C] (P : C → Finset C → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (S : Finset C) (i : ℕ) :
    0 ≤ purchaseProfile P r S i := by
  unfold purchaseProfile
  split_ifs
  · exact Finset.sum_nonneg (fun x _ => hP.nonneg x S)
  · exact le_rfl

open RevenueOrdered.PurchaseRatio in
lemma N_succ_le {C : Type*} [Fintype C] (P : C → Finset C → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (S : Finset C) (i : ℕ) (hi : 1 ≤ i) :
    purchaseProfile P r S (i + 1) ≤ purchaseProfile P r S i := by
  by_cases hk : i + 1 ≤ RevenueOrdered.Ratio.numVals r
  · unfold purchaseProfile
    rw [if_pos ⟨by omega, hk⟩, if_pos ⟨hi, by omega⟩]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, le_trans (level_mono r i hi hk) hx.2⟩
    · intro x _ _
      exact hP.nonneg x S
  · have : purchaseProfile P r S (i + 1) = 0 := by
      unfold purchaseProfile
      rw [if_neg (by omega)]
    rw [this]
    exact N_nonneg P hP r S i

open RevenueOrdered.PurchaseRatio in
lemma N_anti {C : Type*} [Fintype C] (P : C → Finset C → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (S : Finset C) (i : ℕ) (hi : 1 ≤ i) :
    ∀ j, i ≤ j → purchaseProfile P r S j ≤ purchaseProfile P r S i := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact le_trans (N_succ_le P hP r S j (by omega)) ih

open RevenueOrdered.PurchaseRatio in
lemma N_level_le {C : Type*} [Fintype C] (P : C → Finset C → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤
      RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r i) := by
  classical
  unfold purchaseProfile
  rw [if_pos ⟨hi1, hik⟩]
  set T := S.filter (fun x => RevenueOrdered.Ratio.level r i ≤ r x) with hT
  set U := RevenueOrdered.Ratio.roSet r i with hU
  have hTU : T ⊆ U := by
    intro x hx
    simp only [hT, Finset.mem_filter] at hx
    simp [hU, RevenueOrdered.Ratio.roSet, hx.2]
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hlevU : ∀ x ∈ U, RevenueOrdered.Ratio.level r i ≤ r x := by
    intro x hx
    simpa [hU, RevenueOrdered.Ratio.roSet] using hx
  have hlev0 := level_nonneg r hr i
  have h1 : ∑ x ∈ T, P x S ≤ ∑ x ∈ T, P x T :=
    Finset.sum_le_sum (fun x hx => hP.mono T S x hTS hx)
  have h2 : ∑ x ∈ T, P x T ≤ ∑ x ∈ U, P x U := by
    have := hP.noPurchase_mono T U hTU
    unfold RevenueOrdered.Ratio.noPurchase at this
    linarith
  have h3 : ∑ x ∈ U, P x U * RevenueOrdered.Ratio.level r i ≤ ∑ x ∈ U, P x U * r x :=
    Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hlevU x hx) (hP.nonneg x U))
  calc (∑ x ∈ T, P x S) * RevenueOrdered.Ratio.level r i
      ≤ (∑ x ∈ U, P x U) * RevenueOrdered.Ratio.level r i :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) hlev0
    _ = ∑ x ∈ U, P x U * RevenueOrdered.Ratio.level r i := by rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ U, P x U * r x := h3
    _ = RevenueOrdered.Ratio.revenue P r U := rfl

lemma telescope (f : ℕ → ℝ) : ∀ m : ℕ,
    ∑ l ∈ Finset.Icc 1 m, (f l - f (l - 1)) = f m - f 0
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), telescope f m]
    simp

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

open RevenueOrdered.PurchaseRatio in
lemma layer {C : Type*} [Fintype C] (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) :
    RevenueOrdered.Ratio.revenue P r S =
      ∑ l ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r),
        (RevenueOrdered.Ratio.level r l - RevenueOrdered.Ratio.level r (l - 1)) *
          purchaseProfile P r S l := by
  have h1 : ∀ l ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r), purchaseProfile P r S l =
      ∑ x ∈ S, if RevenueOrdered.Ratio.level r l ≤ r x then P x S else 0 := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    unfold purchaseProfile
    rw [if_pos hl, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun l hl => by rw [h1 l hl])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold RevenueOrdered.Ratio.revenue
  refine Finset.sum_congr rfl (fun x _ => ?_)
  calc P x S * r x
      = P x S * ∑ l ∈ Finset.Icc 1 (RevenueOrdered.Ratio.numVals r),
          (if RevenueOrdered.Ratio.level r l ≤ r x then
            RevenueOrdered.Ratio.level r l - RevenueOrdered.Ratio.level r (l - 1) else 0) := by
        rw [key r x]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        split_ifs <;> ring

end FD2F4BF9Aux

open RevenueOrdered.PurchaseRatio in
theorem solution {C : Type*} [Fintype C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (hSopt : RevenueOrdered.Ratio.revenue P r S = RevenueOrdered.Ratio.opt P r)
    (hN1 : 0 < purchaseProfile P r S 1)
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ RevenueOrdered.Ratio.numVals r)
    (hℓpos : 0 < purchaseProfile P r S ℓ)
    (hℓmax : ∀ i, ℓ < i → i ≤ RevenueOrdered.Ratio.numVals r → ¬ 0 < purchaseProfile P r S i) :
    RevenueOrdered.Ratio.opt P r ≤ purchaseRatioSum P r S ℓ * RevenueOrdered.Ratio.roValue P r ∧
      purchaseRatioSum P r S ℓ ≤
        1 + Real.log (purchaseProfile P r S 1 / purchaseProfile P r S ℓ) := by
  set k := RevenueOrdered.Ratio.numVals r with hk
  set N : ℕ → ℝ := fun i => purchaseProfile P r S i with hN
  have hNnn : ∀ i, 0 ≤ N i := fun i => FD2F4BF9Aux.N_nonneg P hP r S i
  -- N vanishes beyond ℓ
  have hzero : ∀ i, ℓ < i → N i = 0 := by
    intro i hi
    by_cases hik : i ≤ k
    · have h1 := not_lt.mp (hℓmax i hi hik)
      have h2 := hNnn i
      show purchaseProfile P r S i = 0
      exact le_antisymm h1 h2
    · show purchaseProfile P r S i = 0
      unfold purchaseProfile
      rw [if_neg (by omega)]
  have hpos : ∀ i, 1 ≤ i → i ≤ ℓ → 0 < N i := by
    intro i h1 h2
    exact lt_of_lt_of_le hℓpos (FD2F4BF9Aux.N_anti P hP r S i h1 ℓ h2)
  have hdiff : ∀ i, 1 ≤ i → 0 ≤ N i - N (i + 1) := by
    intro i hi
    have := FD2F4BF9Aux.N_succ_le P hP r S i hi
    show 0 ≤ purchaseProfile P r S i - purchaseProfile P r S (i + 1)
    linarith
  have hsumeq : purchaseRatioSum P r S ℓ = ∑ i ∈ Finset.Icc 1 ℓ, (N i - N (i + 1)) / N i := rfl
  constructor
  · -- OPT ≤ (∑ ...) * RO
    rw [← hSopt, FD2F4BF9Aux.layer P r S, hsumeq]
    have hab := FD2F4BF9Aux.abel (fun l => RevenueOrdered.Ratio.level r l) N k
    have hk1 : N (k + 1) = 0 := hzero (k + 1) (by omega)
    have hN' : ∀ l, purchaseProfile P r S l = N l := fun l => rfl
    simp only [hN']
    rw [hab, hk1, FD2F4BF9Aux.level_zero]
    simp only [mul_zero, zero_mul, add_zero, sub_zero]
    have hsub : ∑ l ∈ Finset.Icc 1 k, RevenueOrdered.Ratio.level r l * (N l - N (l + 1)) =
        ∑ l ∈ Finset.Icc 1 ℓ, RevenueOrdered.Ratio.level r l * (N l - N (l + 1)) := by
      symm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Icc] at hi ⊢
        omega
      · intro i hi hni
        simp only [Finset.mem_Icc] at hi hni
        have h1 : N i = 0 := hzero i (by omega)
        have h2 : N (i + 1) = 0 := hzero (i + 1) (by omega)
        rw [h1, h2]
        ring
    rw [hsub, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hNi := hpos i hi.1 hi.2
    have hd := hdiff i hi.1
    have hle : N i * RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.roValue P r := by
      have h1 := FD2F4BF9Aux.N_level_le P hP r hr S i hi.1 (by omega)
      have h2 : RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r i) ≤
          RevenueOrdered.Ratio.roValue P r := by
        unfold RevenueOrdered.Ratio.roValue
        exact Finset.le_sup' (fun i => RevenueOrdered.Ratio.revenue P r
          (RevenueOrdered.Ratio.roSet r i)) (Finset.mem_Icc.mpr ⟨hi.1, by omega⟩)
      exact le_trans h1 h2
    have hlev : RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.roValue P r / N i := by
      rw [le_div_iff₀ hNi]
      linarith
    calc RevenueOrdered.Ratio.level r i * (N i - N (i + 1))
        ≤ (RevenueOrdered.Ratio.roValue P r / N i) * (N i - N (i + 1)) :=
          mul_le_mul_of_nonneg_right hlev hd
      _ = (N i - N (i + 1)) / N i * RevenueOrdered.Ratio.roValue P r := by ring
  · rw [hsumeq]
    have hIcc : Finset.Icc 1 ℓ = Finset.Ico 1 (ℓ + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_succ_top hℓ1]
    have hlast : (N ℓ - N (ℓ + 1)) / N ℓ = 1 := by
      rw [hzero (ℓ + 1) (by omega), sub_zero, div_self (ne_of_gt (hpos ℓ hℓ1 le_rfl))]
    rw [hlast]
    have := FD2F4BF9Aux.log_sum N ℓ hℓ1 hpos
    show _ ≤ 1 + Real.log (N 1 / N ℓ)
    linarith
