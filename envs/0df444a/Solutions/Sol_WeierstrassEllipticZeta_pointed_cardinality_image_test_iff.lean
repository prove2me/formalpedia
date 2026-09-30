-- Prove2me | solution 1 for WeierstrassEllipticZeta.pointed_cardinality_image_test_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T23:04:37.903753+00:00
-- url     : https://prove2.me/submissions/f05d4a93-0296-4310-8635-bf85cd45b4a4

import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section

private lemma pointed_subset_maximal_image
    {α β : Type*} (f : α → β) (X : Finset α) (x₀ : α) (hx₀ : x₀ ∈ X)
    (r : ℕ) (hr : 1 ≤ r) (hrX : r ≤ X.card) :
    ∃ Y : Finset α, Y ⊆ X ∧ x₀ ∈ Y ∧ Y.card = r ∧
      (f '' (Y : Set α)).ncard = min r (f '' (X : Set α)).ncard := by
  classical
  have hseed : Set.InjOn f ({x₀} : Set α) := by
    intro x hx y hy _
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  obtain ⟨T, hxT, hTX, himage, hinj⟩ :=
    hseed.exists_subset_injOn_subset_range_eq (Set.singleton_subset_iff.mpr hx₀)
  let t := (X.finite_toSet.subset hTX).toFinset
  have ht : (t : Set α) = T := Set.Finite.coe_toFinset _
  have hxt : x₀ ∈ t := by
    change x₀ ∈ (t : Set α)
    rw [ht]
    exact hxT (Set.mem_singleton x₀)
  have htX : t ⊆ X := by
    intro x hx
    apply hTX
    rwa [← ht]
  have htcard : t.card = (f '' (X : Set α)).ncard := by
    rw [← Set.ncard_coe_finset, ht, ← himage, hinj.ncard_image]
  rcases le_total r t.card with hrt | htr
  · obtain ⟨Y, hxY, hYt, hYr⟩ := Finset.exists_subsuperset_card_eq
      (Finset.singleton_subset_iff.mpr hxt) (by simpa using hr) hrt
    refine ⟨Y, hYt.trans htX, hxY (Finset.mem_singleton_self _), hYr, ?_⟩
    have hinjY : Set.InjOn f (Y : Set α) := hinj.mono (by
      intro x hx
      rw [← ht]
      exact hYt hx)
    rw [hinjY.ncard_image, Set.ncard_coe_finset, hYr,
      min_eq_left (hrt.trans_eq htcard)]
  · obtain ⟨Y, htY, hYX, hYr⟩ := Finset.exists_subsuperset_card_eq htX htr hrX
    refine ⟨Y, hYX, htY hxt, hYr, ?_⟩
    have himageY : f '' (Y : Set α) = f '' (X : Set α) := by
      apply Set.Subset.antisymm (Set.image_mono hYX)
      rw [← himage, ← ht]
      exact Set.image_mono htY
    rw [himageY, min_eq_right (htcard.symm.le.trans htr)]

theorem solution
    {α β : Type*} (f : α → β) (X : Finset α) (x₀ : α) (hx₀ : x₀ ∈ X)
    (w A B : ℝ) (hw : 0 < w) (hB : 0 ≤ B) (hBA : B ≤ A) :
    (w * X.card ≤ A ∨ w * (f '' (X : Set α)).ncard ≤ B) ↔
      ∀ Y : Finset α, Y ⊆ X → x₀ ∈ Y → Y.card = ⌊A / w⌋₊ + 1 →
        w * (f '' (Y : Set α)).ncard ≤ B := by
  classical
  let r := ⌊A / w⌋₊ + 1
  have hAr : A < w * r := by
    have h : A / w < (r : ℝ) := by
      simpa [r] using Nat.lt_floor_add_one (A / w)
    simpa only [mul_comm] using (div_lt_iff₀ hw).mp h
  constructor
  · rintro (hpoint | hperiod) Y hYX _ hYr
    · have hYcard : r ≤ X.card := hYr.symm.le.trans (Finset.card_le_card hYX)
      have hle := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hYcard) hw.le
      exact False.elim (hAr.not_ge (hle.trans hpoint))
    · have hcount := Set.ncard_le_ncard (Set.image_mono hYX) (X.finite_toSet.image f)
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount) hw.le).trans hperiod
  · intro htest
    by_contra h
    obtain ⟨hpoint, hperiod⟩ := not_or.mp h
    have hrX : r ≤ X.card := by
      apply Nat.add_one_le_iff.mpr
      apply (Nat.floor_lt (div_nonneg (hB.trans hBA) hw.le)).mpr
      apply (div_lt_iff₀ hw).mpr
      simpa only [mul_comm] using lt_of_not_ge hpoint
    obtain ⟨Y, hYX, hxY, hYr, hYimage⟩ :=
      pointed_subset_maximal_image f X x₀ hx₀ r (Nat.succ_pos _) hrX
    have hY := htest Y hYX hxY hYr
    rw [hYimage] at hY
    rcases le_total r (f '' (X : Set α)).ncard with hrs | hsr
    · rw [min_eq_left hrs] at hY
      exact (hBA.trans_lt hAr).not_ge hY
    · rw [min_eq_right hsr] at hY
      exact hperiod hY
