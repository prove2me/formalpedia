-- Prove2me | solution 1 for PersistClust.Count.window_census_abstract
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T18:10:50.345714+00:00
-- url     : https://prove2.me/submissions/fcc43f8b-7c13-414b-beb9-a3e78c2184d7

import Mathlib

private theorem pcwc_mergeCount_mono {U W : Type*} (g : U → W) {S S' : Set U} (h : S ⊆ S') :
    S.encard + (g '' S').encard ≤ S'.encard + (g '' S).encard := by
  have hsplit : S' = S ∪ (S' \ S) := (Set.union_diff_cancel h).symm
  have himg : g '' S' ⊆ g '' S ∪ g '' (S' \ S) := by
    rw [← Set.image_union, ← hsplit]
  have h1 : (g '' S').encard ≤ (g '' S).encard + (S' \ S).encard :=
    (Set.encard_le_encard himg).trans
      ((Set.encard_union_le _ _).trans (add_le_add le_rfl (Set.encard_image_le g _)))
  have h2 : S'.encard = S.encard + (S' \ S).encard := by
    rw [add_comm]
    exact (Set.encard_diff_add_encard_of_subset h).symm
  calc S.encard + (g '' S').encard
      ≤ S.encard + ((g '' S).encard + (S' \ S).encard) := add_le_add le_rfl h1
    _ = (S.encard + (S' \ S).encard) + (g '' S).encard := by ac_rfl
    _ = S'.encard + (g '' S).encard := by rw [← h2]

/-- An injective map preserves the merge-count functional: for `e` injective with
`g' ∘ e = e'' ∘ g` (`e''` injective on the relevant images), `|e '' S| = |S|` and
`|g' '' (e '' S)| = |g '' S|`. -/
private theorem pcwc_mergeCount_transport {U W U' W' : Type*} (g : U → W) (g' : U' → W')
    (e : U → U') (e' : W → W') (he : Function.Injective e) (he' : Function.Injective e')
    (hcomm : ∀ u, g' (e u) = e' (g u)) (S : Set U) :
    (e '' S).encard = S.encard ∧ (g' '' (e '' S)).encard = (g '' S).encard := by
  refine ⟨he.encard_image S, ?_⟩
  have himg : g' '' (e '' S) = e' '' (g '' S) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun u _ => hcomm u
  rw [himg]
  exact he'.encard_image _

theorem solution {U W U' W' : Type*} (g : U → W) (g' : U' → W')
    (e : U → U') (e' : W → W') (he : Function.Injective e) (he' : Function.Injective e')
    (hcomm : ∀ u, g' (e u) = e' (g u)) {SL SR : Set U} {TL TR : Set U'}
    (hL : e '' SL ⊆ TL) (hR : TR ⊆ e '' SR) :
    SL.encard + (g '' SR).encard + (g' '' TL).encard + TR.encard ≤
      SR.encard + (g '' SL).encard + TL.encard + (g' '' TR).encard := by
  have hA := pcwc_mergeCount_mono g' hL
  have hB := pcwc_mergeCount_mono g' hR
  obtain ⟨hL1, hL2⟩ := pcwc_mergeCount_transport g g' e e' he he' hcomm SL
  obtain ⟨hR1, hR2⟩ := pcwc_mergeCount_transport g g' e e' he he' hcomm SR
  rw [hL1, hL2] at hA
  rw [hR1, hR2] at hB
  -- hA : |SL| + |g' TL| ≤ |TL| + |g SL| ;  hB : |TR| + |g SR| ≤ |SR| + |g' TR|
  calc SL.encard + (g '' SR).encard + (g' '' TL).encard + TR.encard
      = (SL.encard + (g' '' TL).encard) + (TR.encard + (g '' SR).encard) := by ac_rfl
    _ ≤ (TL.encard + (g '' SL).encard) + (SR.encard + (g' '' TR).encard) :=
        add_le_add hA hB
    _ = SR.encard + (g '' SL).encard + TL.encard + (g' '' TR).encard := by ac_rfl

