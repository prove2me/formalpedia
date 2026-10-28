-- Prove2me | solution 1 for PrivateRelease.VCLowerBound.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:30:25.042167+00:00
-- url     : https://prove2.me/submissions/abc2463d-ed38-4b63-a294-3ace1432ac2c

import Mathlib
import Definitions.Def_PrivateRelease_VCLowerBound_Construction

open PrivateRelease.VCLowerBound in
theorem solution {X : Type} [DecidableEq X] (S : Finset X) (m : ℕ) (hS : S.card = 2 * m)
    (T T' : Finset X) (hT : T ∈ DS S m) (hT' : T' ∈ DS S m) (φ : X → Bool)
    (hφ : IsIndicatorOn S T φ) :
    countQF φ T - countQF φ T' = ((symmDiff T T').card : ℝ) / (S.card : ℝ) := by
  rw [DS, Finset.mem_powersetCard] at hT hT'
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have e1 : T = ∅ := Finset.card_eq_zero.mp hT.2
    have e2 : T' = ∅ := Finset.card_eq_zero.mp hT'.2
    subst e1 e2
    simp
  have hm : (m : ℝ) ≠ 0 := by positivity
  have hf1 : T.filter (fun x => φ x = true) = T :=
    Finset.filter_true_of_mem (fun x hx => (hφ x (hT.1 hx)).mpr hx)
  have hf2 : T'.filter (fun x => φ x = true) = T' ∩ T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hφ x (hT'.1 h1)).mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hφ x (hT'.1 h1)).mpr h2⟩
  have e1 : countQF φ T = 1 := by
    unfold countQF; rw [hf1, hT.2, div_self hm]
  have e2 : countQF φ T' = ((T' ∩ T).card : ℝ) / m := by
    unfold countQF; rw [hf2, hT'.2]
  have hsd : (symmDiff T T').card = (T \ T').card + (T' \ T).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have ha : ((T \ T').card : ℝ) + (T ∩ T').card = m := by
    rw [← hT.2]; exact_mod_cast Finset.card_sdiff_add_card_inter T T'
  have hb : ((T' \ T).card : ℝ) + (T' ∩ T).card = m := by
    rw [← hT'.2]; exact_mod_cast Finset.card_sdiff_add_card_inter T' T
  have hii : ((T ∩ T').card : ℝ) = (T' ∩ T).card := by rw [Finset.inter_comm]
  have hdm : ((T' ∩ T).card : ℝ) / m * m = (T' ∩ T).card := div_mul_cancel₀ _ hm
  rw [e1, e2, hsd, hS]
  push_cast
  rw [eq_div_iff (by positivity)]
  linear_combination (-2 : ℝ) * hdm - ha - hb + hii
