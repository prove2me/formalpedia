-- Prove2me | solution 1 for RevenueOrdered.Tightness.tightP_noPurchase_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:49:44.323061+00:00
-- url     : https://prove2.me/submissions/8684c1e5-6399-41d2-9e66-211259ec3fa7

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

set_option autoImplicit false

open RevenueOrdered.Tightness in
/-- The set of row-minimal elements of `S`. -/
noncomputable def tightMinSet_8252 (k : ℕ) (S : Finset (TightProduct k)) : Finset (TightProduct k) :=
  S.filter (fun x => ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val)

open RevenueOrdered.Tightness in
theorem tightP_sum_eq_8252 (k : ℕ) (ε : ℝ) (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S =
      ∑ i ∈ S.image (fun x => x.val.1), ε ^ i.val := by
  classical
  have h1 : ∑ x ∈ S, tightP k ε x S = ∑ x ∈ tightMinSet_8252 k S, ε ^ x.val.1.val := by
    unfold tightMinSet_8252
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro x hx
    unfold tightP
    by_cases h : ∀ y ∈ S, y.val.1 = x.val.1 → x.val.2.val ≤ y.val.2.val
    · rw [if_pos ⟨hx, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  have hinj : Set.InjOn (fun x : TightProduct k => x.val.1) (tightMinSet_8252 k S : Set _) := by
    intro x hx y hy hxy
    simp only [tightMinSet_8252, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    have hxy' : x.val.1 = y.val.1 := hxy
    have a := hx.2 y hy.1 hxy'.symm
    have b := hy.2 x hx.1 hxy'
    apply Subtype.ext
    apply Prod.ext hxy'
    apply Fin.ext
    omega
  have himg : (tightMinSet_8252 k S).image (fun x => x.val.1) = S.image (fun x => x.val.1) := by
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
      unfold tightMinSet_8252
      rw [Finset.mem_filter]
      refine ⟨hm.1, ?_⟩
      intro y hy hyrow
      exact hmin y (Finset.mem_filter.mpr ⟨hy, hyrow.trans hm.2⟩)
  rw [h1, ← himg, Finset.sum_image hinj]

open RevenueOrdered.Tightness in
theorem solution (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') :
    RevenueOrdered.Ratio.noPurchase (tightP k ε) S' ≤ RevenueOrdered.Ratio.noPurchase (tightP k ε) S := by
  unfold RevenueOrdered.Ratio.noPurchase
  rw [tightP_sum_eq_8252, tightP_sum_eq_8252]
  have : ∑ i ∈ S.image (fun x => x.val.1), ε ^ i.val ≤
      ∑ i ∈ S'.image (fun x => x.val.1), ε ^ i.val :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hSS')
      (fun i _ _ => by positivity)
  linarith
