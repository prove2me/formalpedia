-- Prove2me | solution 1 for PersistClust.Count.merge_count_mono
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T18:05:52.169886+00:00
-- url     : https://prove2.me/submissions/c0316ae0-6d93-44f7-89d2-fd5b98590d9d

import Mathlib

theorem solution {U W : Type*} (g : U → W) {S S' : Set U} (h : S ⊆ S') :
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

