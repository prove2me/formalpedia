-- Prove2me | solution 1 for RiskUncSets.Distortion.second_differences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:37:16.270289+00:00
-- url     : https://prove2.me/submissions/41bb94c4-80ae-41c1-a077-236127b56f1e

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

set_option autoImplicit false

open RiskUncSets.Distortion in
lemma ae5377d0_card_lt {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    ({ω : Fin N | (ω : ℕ) < k}).ncard = k := by
  rw [← Set.ncard_image_of_injective _ Fin.val_injective]
  have h : Fin.val '' {ω : Fin N | (ω : ℕ) < k} = ((Finset.range k : Finset ℕ) : Set ℕ) := by
    ext n
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨ω, h, rfl⟩
      exact h
    · intro h
      exact ⟨⟨n, by omega⟩, h, rfl⟩
  rw [h, Set.ncard_coe_finset, Finset.card_range]

open RiskUncSets.Distortion in
theorem solution {N : ℕ} (g : Set (Fin N) → ℝ) (hsub : IsSubmodularSF g)
    (hlaw : ∀ A B : Set (Fin N), A.ncard = B.ncard → g A = g B)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i + 1 ≤ N) :
    g {ω : Fin N | (ω : ℕ) < i + 1} - g {ω : Fin N | (ω : ℕ) < i} ≤
      g {ω : Fin N | (ω : ℕ) < i} - g {ω : Fin N | (ω : ℕ) < i - 1} := by
  set b : Fin N := ⟨i, by omega⟩ with hb
  have hbC : b ∉ {ω : Fin N | (ω : ℕ) < i - 1} := by
    simp only [Set.mem_setOf_eq, hb]
    omega
  have hB : (insert b {ω : Fin N | (ω : ℕ) < i - 1}).ncard = i := by
    rw [Set.ncard_insert_of_notMem hbC (Set.toFinite _), ae5377d0_card_lt (i - 1) (by omega)]
    omega
  have hU : {ω : Fin N | (ω : ℕ) < i} ∪ insert b {ω : Fin N | (ω : ℕ) < i - 1}
      = {ω : Fin N | (ω : ℕ) < i + 1} := by
    ext ω
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, hb, Fin.ext_iff]
    omega
  have hI : {ω : Fin N | (ω : ℕ) < i} ∩ insert b {ω : Fin N | (ω : ℕ) < i - 1}
      = {ω : Fin N | (ω : ℕ) < i - 1} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_setOf_eq, hb, Fin.ext_iff]
    omega
  have h1 := hsub {ω : Fin N | (ω : ℕ) < i} (insert b {ω : Fin N | (ω : ℕ) < i - 1})
  have h2 : g (insert b {ω : Fin N | (ω : ℕ) < i - 1}) = g {ω : Fin N | (ω : ℕ) < i} :=
    hlaw _ _ (by rw [hB, ae5377d0_card_lt i (by omega)])
  rw [hU, hI, h2] at h1
  linarith
