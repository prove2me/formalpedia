-- Prove2me | solution 1 for QBFBackdoor.selector_observation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:41:28.933978+00:00
-- url     : https://prove2.me/submissions/c853eca4-82b1-455f-be42-0044befac633

import Mathlib

theorem solution (k p : ℕ) (T : Finset (Fin k)) :
    (∃ z : Fin k → Fin p → Bool, ∀ w : Fin p → Bool, ∃ s ∈ T, z s = w) ↔ 2 ^ p ≤ T.card := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    have hsub : (Finset.univ : Finset (Fin p → Bool)) ⊆ T.image z := fun w _ => by
      obtain ⟨s, hs, rfl⟩ := hz w
      exact Finset.mem_image_of_mem z hs
    have h1 := Finset.card_le_card hsub
    have h2 : (T.image z).card ≤ T.card := Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
    omega
  · intro h
    obtain ⟨e⟩ : Nonempty ((Fin p → Bool) ↪ T) :=
      Function.Embedding.nonempty_of_card_le (by simpa using h)
    refine ⟨fun s => if hs : ∃ w, ((e w : T) : Fin k) = s then hs.choose else fun _ => false,
      fun w => ⟨e w, (e w).2, ?_⟩⟩
    have hs : ∃ w', ((e w' : T) : Fin k) = e w := ⟨w, rfl⟩
    simp only [dif_pos hs]
    exact e.injective (Subtype.ext hs.choose_spec)
