-- Prove2me | solution 1 for RevenueOrdered.Tightness.revenue_ordered_bounds_tight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T07:36:48.178638+00:00
-- url     : https://prove2.me/submissions/c4239e3a-d44a-4844-8e45-38037ccdac4e

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

set_option autoImplicit false

open RevenueOrdered.Tightness in
/-- The set of row-minimal elements of `S`. -/
noncomputable def tbMin_be49 (k : ℕ) (S : Finset (TightProduct k)) : Finset (TightProduct k) :=
  S.filter (fun x => ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val)

open RevenueOrdered.Tightness in
theorem tbInj_be49 (k : ℕ) (S : Finset (TightProduct k)) :
    Set.InjOn (fun x : TightProduct k => x.val.1.val) (tbMin_be49 k S : Set (TightProduct k)) := by
  intro x hx y hy hxy
  simp only [tbMin_be49, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  have hxy' : x.val.1 = y.val.1 := Fin.ext hxy
  have a := hx.2 y hy.1 hxy'.symm
  have b := hy.2 x hx.1 hxy'
  apply Subtype.ext
  apply Prod.ext hxy'
  exact Fin.ext (le_antisymm a b)

open RevenueOrdered.Tightness in
theorem tbImgSub_be49 (k : ℕ) (S : Finset (TightProduct k)) :
    (tbMin_be49 k S).image (fun x : TightProduct k => x.val.1.val) ⊆ Finset.Icc 1 k := by
  intro i hi
  rw [Finset.mem_image] at hi
  obtain ⟨x, _, rfl⟩ := hi
  rw [Finset.mem_Icc]
  have h1 := x.property
  have h2 := x.val.1.isLt
  constructor <;> omega

open RevenueOrdered.Tightness in
theorem tbCard_be49 (k : ℕ) (S : Finset (TightProduct k)) : (tbMin_be49 k S).card ≤ k := by
  have h := Finset.card_le_card (tbImgSub_be49 k S)
  rw [Finset.card_image_of_injOn (tbInj_be49 k S)] at h
  simpa using h

open RevenueOrdered.Tightness in
theorem tbSum_be49 (k : ℕ) (ε : ℝ) (S : Finset (TightProduct k)) (f : TightProduct k → ℝ) :
    ∑ x ∈ S, tightP k ε x S * f x = ∑ x ∈ tbMin_be49 k S, ε ^ x.val.1.val * f x := by
  unfold tbMin_be49
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro x hx
  unfold tightP
  by_cases h : ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val
  · rw [if_pos ⟨hx, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]; simp

open RevenueOrdered.Tightness in
theorem tbGeom_be49 (ε : ℝ) (k : ℕ) :
    (1 - ε) * ∑ i ∈ Finset.Icc 1 k, ε ^ i = ε - ε ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

open RevenueOrdered.Tightness in
theorem tbSumLe_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S ≤ 1 := by
  have hpos : 0 < 1 - ε := by linarith
  have h0 : ∑ x ∈ S, tightP k ε x S = ∑ x ∈ tbMin_be49 k S, ε ^ x.val.1.val := by
    have := tbSum_be49 k ε S (fun _ => 1)
    simpa using this
  rw [h0]
  have h1 : ∑ x ∈ tbMin_be49 k S, ε ^ x.val.1.val ≤ ∑ i ∈ Finset.Icc 1 k, ε ^ i := by
    rw [← Finset.sum_image (f := fun i => ε ^ i) (g := fun x : TightProduct k => x.val.1.val)
      (fun a ha b hb h => tbInj_be49 k S ha hb h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (tbImgSub_be49 k S)
    intro i _ _
    positivity
  have h2 : ∑ i ∈ Finset.Icc 1 k, ε ^ i ≤ ε / (1 - ε) := by
    rw [le_div_iff₀ hpos, mul_comm, tbGeom_be49]
    have : 0 < ε ^ (k + 1) := pow_pos hε _
    linarith
  have h3 : ε / (1 - ε) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  linarith

open RevenueOrdered.Tightness in
theorem tbAnti_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') (x : TightProduct k) (hx : x ∈ S) :
    tightP k ε x S' ≤ tightP k ε x S := by
  unfold tightP
  by_cases h : x ∈ S' ∧ ∀ y ∈ S', y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val
  · have h2 : x ∈ S ∧ ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val :=
      ⟨hx, fun y hy => h.2 y (hSS' hy)⟩
    rw [if_pos h, if_pos h2]
  · rw [if_neg h]
    split_ifs <;> positivity

open RevenueOrdered.Tightness in
theorem tbSumEq_be49 (k : ℕ) (ε : ℝ) (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S =
      ∑ i ∈ S.image (fun x => x.val.1), ε ^ i.val := by
  classical
  have h1 : ∑ x ∈ S, tightP k ε x S = ∑ x ∈ tbMin_be49 k S, ε ^ x.val.1.val := by
    have := tbSum_be49 k ε S (fun _ => 1)
    simpa using this
  have himg : (tbMin_be49 k S).image (fun x => x.val.1) = S.image (fun x => x.val.1) := by
    apply Finset.Subset.antisymm
    · apply Finset.image_subset_image
      exact Finset.filter_subset _ _
    · intro i hi
      rw [Finset.mem_image] at hi ⊢
      obtain ⟨x0, hx0, rfl⟩ := hi
      have hne : (S.filter (fun y => y.val.1 = x0.val.1)).Nonempty :=
        ⟨x0, Finset.mem_filter.mpr ⟨hx0, rfl⟩⟩
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ (fun y : TightProduct k => y.val.2.val) hne
      rw [Finset.mem_filter] at hm
      refine ⟨m, ?_, hm.2⟩
      unfold tbMin_be49
      rw [Finset.mem_filter]
      refine ⟨hm.1, ?_⟩
      intro y hy hyrow
      exact hmin y (Finset.mem_filter.mpr ⟨hy, hyrow.trans hm.2⟩)
  have hinj : Set.InjOn (fun x : TightProduct k => x.val.1) (tbMin_be49 k S : Set _) := by
    intro x hx y hy hxy
    have := tbInj_be49 k S hx hy (congrArg Fin.val hxy)
    exact this
  rw [h1, ← himg, Finset.sum_image hinj]

open RevenueOrdered.Tightness in
theorem tbNoP_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') :
    RevenueOrdered.Ratio.noPurchase (tightP k ε) S' ≤ RevenueOrdered.Ratio.noPurchase (tightP k ε) S := by
  unfold RevenueOrdered.Ratio.noPurchase
  rw [tbSumEq_be49, tbSumEq_be49]
  have : ∑ i ∈ S.image (fun x => x.val.1), ε ^ i.val ≤
      ∑ i ∈ S'.image (fun x => x.val.1), ε ^ i.val :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hSS')
      (fun i _ _ => by positivity)
  linarith

open RevenueOrdered.Tightness in
theorem tbReg_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    RevenueOrdered.Tightness.IsRegular (tightP k ε) where
  nonneg := by
    intro x S
    unfold tightP
    split_ifs <;> positivity
  noPurchase_nonneg := by
    intro S
    unfold RevenueOrdered.Ratio.noPurchase
    linarith [tbSumLe_be49 k ε hε hε2 S]
  eq_zero_of_not_mem := by
    intro x S hx
    unfold tightP
    rw [if_neg (fun h => hx h.1)]
  sum_le_one := tbSumLe_be49 k ε hε hε2
  antitone := fun S S' h x hx => tbAnti_be49 k ε hε S S' h x hx
  noPurchase_antitone := fun S S' h => tbNoP_be49 k ε hε S S' h

open RevenueOrdered.Tightness in
theorem tbRevLe_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S * tightRevenue k ε x ≤ k := by
  rw [tbSum_be49]
  have hterm : ∀ x ∈ tbMin_be49 k S, ε ^ x.val.1.val * tightRevenue k ε x ≤ 1 := by
    intro x _
    unfold tightRevenue
    have hj : x.val.2.val ≤ x.val.1.val := x.property.2
    have h1 : ε ^ x.val.1.val ≤ ε ^ x.val.2.val := pow_le_pow_of_le_one hε.le (by linarith) hj
    have h2 : 0 < ε ^ x.val.2.val := pow_pos hε _
    calc ε ^ x.val.1.val * (ε ^ x.val.2.val)⁻¹
        ≤ ε ^ x.val.2.val * (ε ^ x.val.2.val)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ h2.ne'
  calc _ ≤ ∑ x ∈ tbMin_be49 k S, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((tbMin_be49 k S).card : ℝ) := by simp
    _ ≤ k := by exact_mod_cast tbCard_be49 k S

open RevenueOrdered.Tightness in
theorem tbDiagCard_be49 (k : ℕ) : (diagonalSet k).card = k := by
  have hmin : tbMin_be49 k (diagonalSet k) = diagonalSet k := by
    unfold tbMin_be49
    apply Finset.filter_true_of_mem
    intro x hx y hy hrow
    simp only [diagonalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have h1 : y.val.2 = y.val.1 := hy
    have h2 : x.val.2 = x.val.1 := hx
    rw [h1, hrow, h2]
  have hinj := tbInj_be49 k (diagonalSet k)
  rw [hmin] at hinj
  have himg : (diagonalSet k).image (fun x : TightProduct k => x.val.1.val) = Finset.Icc 1 k := by
    apply Finset.Subset.antisymm
    · have := tbImgSub_be49 k (diagonalSet k)
      rwa [hmin] at this
    · intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_image]
      refine ⟨⟨(⟨i, by omega⟩, ⟨i, by omega⟩), hi.1, le_rfl⟩, ?_, rfl⟩
      simp [diagonalSet]
  rw [← Finset.card_image_of_injOn hinj, himg]
  simp

open RevenueOrdered.Tightness in
theorem tbDiag_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∑ x ∈ diagonalSet k, tightP k ε x (diagonalSet k) * tightRevenue k ε x = k := by
  rw [tbSum_be49]
  have hmin : tbMin_be49 k (diagonalSet k) = diagonalSet k := by
    unfold tbMin_be49
    apply Finset.filter_true_of_mem
    intro x hx y hy hrow
    simp only [diagonalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have h1 : y.val.2 = y.val.1 := hy
    have h2 : x.val.2 = x.val.1 := hx
    rw [h1, hrow, h2]
  rw [hmin]
  have hterm : ∀ x ∈ diagonalSet k, ε ^ x.val.1.val * tightRevenue k ε x = 1 := by
    intro x hx
    simp only [diagonalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h2 : x.val.2.val = x.val.1.val := by rw [hx]
    unfold tightRevenue
    rw [h2]
    exact mul_inv_cancel₀ (pow_pos hε _).ne'
  rw [Finset.sum_congr rfl hterm]
  simp [tbDiagCard_be49]

open RevenueOrdered.Tightness in
theorem tbNum_be49 (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    numRevenues (tightRevenue k ε) = k := by
  have himg : revenueValues (tightRevenue k ε) =
      (Finset.Icc 1 k).image (fun j : ℕ => (ε ^ j)⁻¹) := by
    ext y
    simp only [revenueValues, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨x, rfl⟩
      have h1 := x.property
      have h2 := x.val.1.isLt
      exact ⟨x.val.2.val, ⟨h1.1, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨⟨(⟨k, by omega⟩, ⟨j, by omega⟩), hj1, hj2⟩, rfl⟩
  unfold numRevenues
  rw [himg, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : ε ^ a = ε ^ b := inv_injective hab
    exact pow_right_injective₀ hε (by linarith) h

open RevenueOrdered.Tightness in
theorem tbSortedMem_be49 {C : Type} [Fintype C] [DecidableEq C] (r : C → ℝ)
    (i : Fin (numRevenues r)) : ∃ x : C, r x = sortedRevenue r i := by
  have : sortedRevenue r i ∈ revenueValues r := by
    unfold sortedRevenue; exact Finset.orderEmbOfFin_mem _ _ _
  unfold revenueValues at this
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp this
  exact ⟨x, hx⟩

open RevenueOrdered.Tightness in
theorem tbGapLe_be49 {C : Type} [Fintype C] [DecidableEq C] (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    revenueGapSum r ≤ numRevenues r := by
  have hpos : ∀ i : Fin (numRevenues r), 0 < sortedRevenue r i := by
    intro i
    obtain ⟨x, hx⟩ := tbSortedMem_be49 r i
    rw [← hx]; exact hr x
  have hprev : ∀ i, 0 ≤ prevRevenue r i := by
    intro i; unfold prevRevenue; split_ifs with h
    · exact le_rfl
    · exact (hpos _).le
  have key : ∀ i : Fin (numRevenues r),
      (sortedRevenue r i - prevRevenue r i) / sortedRevenue r i ≤ 1 := by
    intro i
    rw [div_le_one (hpos i)]; linarith [hprev i]
  unfold revenueGapSum
  calc _ ≤ ∑ i : Fin (numRevenues r), (1 : ℝ) := Finset.sum_le_sum (fun i _ => key i)
    _ = numRevenues r := by simp

open RevenueOrdered.Tightness in
theorem tbPGapLe_be49 {C : Type} [Fintype C] [DecidableEq C] (P : C → Finset C → ℝ)
    (hP : ∀ x S, 0 ≤ P x S) (r : C → ℝ) (S : Finset C) :
    purchaseGapSum P r S ≤ numRevenues r := by
  have hN : ∀ i, 0 ≤ purchaseAbove P r S i := fun i => Finset.sum_nonneg (fun x _ => hP x S)
  have hN' : ∀ i, 0 ≤ nextPurchaseAbove P r S i := by
    intro i; unfold nextPurchaseAbove; split_ifs
    · exact hN _
    · exact le_rfl
  have key : ∀ i, (purchaseAbove P r S i - nextPurchaseAbove P r S i) / purchaseAbove P r S i ≤ 1 := by
    intro i
    rcases (hN i).lt_or_eq with h | h
    · rw [div_le_one h]; linarith [hN' i]
    · rw [← h]; simp
  unfold purchaseGapSum
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun i _ => key i)).trans ?_
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

open RevenueOrdered.Tightness in
theorem tbMinLe_be49 {C : Type} [Fintype C] [DecidableEq C] (r : C → ℝ) (x : C)
    (h : 0 < numRevenues r) : sortedRevenue r ⟨0, h⟩ ≤ r x := by
  have hm : r x ∈ Set.range (sortedRevenue r) := by
    have h := Finset.range_orderEmbOfFin (revenueValues r) (rfl : (revenueValues r).card = numRevenues r)
    have h2 : r x ∈ ((revenueValues r : Finset ℝ) : Set ℝ) := by simp [revenueValues]
    rw [← h] at h2
    exact h2
  obtain ⟨i, hi⟩ := hm
  rw [← hi]
  exact (sortedRevenue r).monotone (by rw [Fin.le_def]; simp)

open RevenueOrdered.Tightness in
theorem tbN1_be49 (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ i : Fin (numRevenues (tightRevenue k ε)), i.val = 0 ∧
      0 < purchaseAbove (tightP k ε) (tightRevenue k ε) (diagonalSet k) i := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hn := numRevenues_pos (tightRevenue k ε)
  refine ⟨⟨0, hn⟩, rfl, ?_⟩
  set x0 : TightProduct k := ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), le_rfl, le_rfl⟩ with hx0
  have hx0d : x0 ∈ diagonalSet k := by simp [diagonalSet, hx0]
  have hP : tightP k ε x0 (diagonalSet k) = ε ^ 1 := by
    have hc : x0 ∈ diagonalSet k ∧ ∀ y ∈ diagonalSet k, y.val.1 = x0.val.1 →
        x0.val.2.val ≤ y.val.2.val := ⟨hx0d, fun y _ _ => y.property.1⟩
    unfold tightP
    rw [if_pos hc]
  unfold purchaseAbove
  calc 0 < tightP k ε x0 (diagonalSet k) := by rw [hP]; positivity
    _ ≤ _ := by
      apply Finset.single_le_sum (f := fun x => tightP k ε x (diagonalSet k))
        (fun x _ => (tbReg_be49 k ε hε hε2).nonneg x _)
      rw [Finset.mem_filter]
      exact ⟨hx0d, tbMinLe_be49 _ x0 hn⟩

open RevenueOrdered.Tightness in
theorem tbRoLe_be49 (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    roValue (tightP k ε) (tightRevenue k ε) ≤ 1 / (1 - ε) := by
  have hε1 : ε < 1 := by linarith
  have hpos : 0 < 1 - ε := by linarith
  unfold roValue
  apply Finset.sup'_le
  intro i _
  obtain ⟨x1, hx1⟩ := tbSortedMem_be49 (tightRevenue k ε) i
  set T := thresholdSet (tightRevenue k ε) i with hT
  set m := x1.val.2.val with hm
  have hm1 : 1 ≤ m := x1.property.1
  have hmem : ∀ x ∈ tbMin_be49 k T, x.val.2.val = m ∧ m ≤ x.val.1.val := by
    intro x hx
    unfold tbMin_be49 at hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxT, hcond⟩ := hx
    rw [hT, thresholdSet, Finset.mem_filter, ← hx1] at hxT
    have h1 : (ε ^ m)⁻¹ ≤ (ε ^ x.val.2.val)⁻¹ := hxT.2
    have hmx : m ≤ x.val.2.val := by
      by_contra hlt
      rw [not_le] at hlt
      have : ε ^ m < ε ^ x.val.2.val := pow_lt_pow_right_of_lt_one₀ hε hε1 hlt
      have h2 : (ε ^ x.val.2.val)⁻¹ < (ε ^ m)⁻¹ := inv_strictAnti₀ (pow_pos hε _) this
      have h3 : (ε ^ m)⁻¹ ≤ (ε ^ x.val.2.val)⁻¹ := h1
      linarith
    have hxm : m ≤ x.val.1.val := le_trans hmx x.property.2
    have hlt1 := x.val.1.isLt
    set y : TightProduct k := ⟨(x.val.1, ⟨m, by omega⟩), hm1, hxm⟩ with hy
    have hyT : y ∈ T := by
      rw [hT, thresholdSet, Finset.mem_filter, ← hx1]
      refine ⟨Finset.mem_univ _, le_of_eq ?_⟩
      simp [tightRevenue, hy, hm]
    have := hcond y hyT rfl
    exact ⟨le_antisymm this hmx, hxm⟩
  show ∑ x ∈ T, tightP k ε x T * tightRevenue k ε x ≤ _
  rw [tbSum_be49]
  have hcongr : ∑ x ∈ tbMin_be49 k T, ε ^ x.val.1.val * tightRevenue k ε x =
      ∑ x ∈ tbMin_be49 k T, (ε ^ x.val.1.val) * (ε ^ m)⁻¹ := by
    apply Finset.sum_congr rfl
    intro x hx
    unfold tightRevenue
    rw [(hmem x hx).1]
  rw [hcongr, ← Finset.sum_mul]
  have hsum : ∑ x ∈ tbMin_be49 k T, ε ^ x.val.1.val ≤ ε ^ m / (1 - ε) := by
    rw [← Finset.sum_image (f := fun i => ε ^ i) (g := fun x : TightProduct k => x.val.1.val)
      (fun a ha b hb h => tbInj_be49 k T ha hb h)]
    calc _ ≤ ∑ i ∈ Finset.Ico m (k + 1), ε ^ i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [Finset.mem_image] at hj
            obtain ⟨x, hx, rfl⟩ := hj
            rw [Finset.mem_Ico]
            exact ⟨(hmem x hx).2, x.val.1.isLt⟩
          · intro j _ _
            positivity
      _ ≤ ε ^ m / (1 - ε) := geom_sum_Ico_le_of_lt_one hε.le hε1
  have hpm : 0 < ε ^ m := pow_pos hε _
  calc (∑ x ∈ tbMin_be49 k T, ε ^ x.val.1.val) * (ε ^ m)⁻¹
      ≤ (ε ^ m / (1 - ε)) * (ε ^ m)⁻¹ := by gcongr
    _ = 1 / (1 - ε) := by field_simp

open RevenueOrdered.Tightness in
theorem solution (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (C : Type) (_ : Fintype C) (_ : DecidableEq C) (_ : Nonempty C)
      (P : C → Finset C → ℝ) (r : C → ℝ) (Sstar : Finset C),
      RevenueOrdered.Tightness.IsRegular P ∧ (∀ x, 0 < r x) ∧ numRevenues r = k ∧
      rev P r Sstar = RevenueOrdered.Ratio.opt P r ∧
      (∃ i : Fin (numRevenues r), i.val = 0 ∧ 0 < purchaseAbove P r Sstar i) ∧
      (k : ℝ) * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r ∧
      revenueGapSum r * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r ∧
      purchaseGapSum P r Sstar * roValue P r < (1 + δ) * RevenueOrdered.Ratio.opt P r := by
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨ε, hε, hε2, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 / (1 - ε) < 1 + δ := by
    set e := min (1 / 2 : ℝ) (δ / (2 * (1 + δ))) with he
    have he0 : 0 < e := lt_min (by norm_num) (by positivity)
    have he1 : e ≤ 1 / 2 := min_le_left _ _
    have he2 : e ≤ δ / (2 * (1 + δ)) := min_le_right _ _
    have he3 : e * (2 * (1 + δ)) ≤ δ := (le_div_iff₀ (by positivity)).mp he2
    refine ⟨e, he0, he1, ?_⟩
    have hp : 0 < 1 - e := by linarith
    rw [div_lt_iff₀ hp]
    nlinarith
  have hreg := tbReg_be49 k ε hε hε2
  have hrpos : ∀ x : TightProduct k, 0 < tightRevenue k ε x := by
    intro x; unfold tightRevenue; positivity
  have hnum := tbNum_be49 k ε hε hε2
  have hopt : RevenueOrdered.Ratio.opt (tightP k ε) (tightRevenue k ε) = k := by
    apply le_antisymm
    · unfold RevenueOrdered.Ratio.opt
      apply Finset.sup'_le
      intro S _
      exact tbRevLe_be49 k ε hε hε2 S
    · have h := Finset.le_sup' (RevenueOrdered.Ratio.revenue (tightP k ε) (tightRevenue k ε))
        (Finset.mem_univ (diagonalSet k))
      have h2 : RevenueOrdered.Ratio.revenue (tightP k ε) (tightRevenue k ε) (diagonalSet k) = k :=
        tbDiag_be49 k ε hε
      unfold RevenueOrdered.Ratio.opt
      rw [← h2]
      exact h
  have hRO0 : 0 ≤ roValue (tightP k ε) (tightRevenue k ε) := by
    unfold roValue
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ⟨0, numRevenues_pos (tightRevenue k ε)⟩))
    unfold rev
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hreg.nonneg x _) (hrpos x).le)
  have hRO := tbRoLe_be49 k ε hε hε2
  have hkRO : (k : ℝ) * roValue (tightP k ε) (tightRevenue k ε) < (1 + δ) * k := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have : roValue (tightP k ε) (tightRevenue k ε) < 1 + δ := lt_of_le_of_lt hRO hεδ
    nlinarith
  refine ⟨TightProduct k, inferInstance, inferInstance, inferInstance, tightP k ε,
    tightRevenue k ε, diagonalSet k, hreg, hrpos, hnum, ?_, tbN1_be49 k ε hε hε2, ?_, ?_, ?_⟩
  · rw [hopt]
    exact tbDiag_be49 k ε hε
  · rw [hopt]; exact hkRO
  · rw [hopt]
    have h1 := tbGapLe_be49 (tightRevenue k ε) hrpos
    rw [hnum] at h1
    calc _ ≤ (k : ℝ) * roValue (tightP k ε) (tightRevenue k ε) := mul_le_mul_of_nonneg_right h1 hRO0
      _ < _ := hkRO
  · rw [hopt]
    have h1 := tbPGapLe_be49 (tightP k ε) hreg.nonneg (tightRevenue k ε) (diagonalSet k)
    rw [hnum] at h1
    calc _ ≤ (k : ℝ) * roValue (tightP k ε) (tightRevenue k ε) := mul_le_mul_of_nonneg_right h1 hRO0
      _ < _ := hkRO
