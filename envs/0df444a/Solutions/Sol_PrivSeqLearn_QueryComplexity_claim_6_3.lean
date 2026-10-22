-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.claim_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:21:42.549065+00:00
-- url     : https://prove2.me/submissions/f55f4edf-4a0f-40a3-85cd-b3921f9df95e

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

open PrivSeqLearn.QueryComplexity

theorem solution (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    L ≤ coverNumber δ (guessUnion ϵ L) := by
  have hLpos : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  -- the sample points `s i = i/L + i ϵ / L ∈ [i/L, i/L + ϵ)`
  set s : Fin L → ℝ := fun i => (i : ℝ) / L + (i : ℝ) * ϵ / L with hs
  have hsG : ∀ i : Fin L, s i ∈ guessUnion ϵ L := by
    intro i
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have hi : (i : ℝ) < L := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ i := by positivity
    constructor
    · simp only [hs]; have : 0 ≤ (i : ℝ) * ϵ / L := by positivity
      linarith
    · simp only [hs]
      have : (i : ℝ) * ϵ / L < ϵ := by
        rw [div_lt_iff₀ hLpos]; nlinarith
      linarith
  -- distinct sample points are more than `δ` apart
  have hsep : ∀ i j : Fin L, (i : ℕ) < j → δ < s j - s i := by
    intro i j hij
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have key : s j - s i = ((j : ℝ) - i) * (1 + ϵ) / L := by
      simp only [hs]; field_simp
    rw [key]
    have h1 : 1 / (L : ℝ) < ((j : ℝ) - i) * (1 + ϵ) / L := by
      apply div_lt_div_of_pos_right _ hLpos
      nlinarith
    linarith
  apply le_csInf
  · refine ⟨L, fun j => (j : ℝ) / L, fun j => (j : ℝ) / L + ϵ, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨i, Set.Ico_subset_Icc_self hi⟩
    · intro j; simp; linarith
  · rintro L' ⟨a, b, hcov, hlen⟩
    have hmem : ∀ i : Fin L, ∃ k : Fin L', s i ∈ Set.Icc (a k) (b k) :=
      fun i => Set.mem_iUnion.1 (hcov (hsG i))
    choose f hf using hmem
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hk := hlen (f i)
      have hfi := hf i
      have hfj := hf j
      rw [← hij] at hfj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · have := hsep i j h
        linarith [hfi.1, hfi.2, hfj.1, hfj.2]
      · have := hsep j i h
        linarith [hfi.1, hfi.2, hfj.1, hfj.2]
    simpa using Fintype.card_le_of_injective f hinj
