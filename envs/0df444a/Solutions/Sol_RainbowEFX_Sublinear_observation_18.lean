-- Prove2me | solution 1 for RainbowEFX.Sublinear.observation_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:34:11.726061+00:00
-- url     : https://prove2.me/submissions/eb8c6ce6-be06-40e2-8f94-f71debec6f59

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX

open RainbowEFX.Sublinear in
theorem solution (r : ℕ) (D : Finset (Fin r → Bool)) :
    ∃ B : Finset (Fin r → Bool), IsRepresentativeSet D B ∧ B.card ≤ r := by
  classical
  let S := Finset.univ.filter (fun ℓ : Fin r => ∃ a ∈ D, a ℓ = true)
  let g : Fin r → (Fin r → Bool) := fun ℓ =>
    if h : ∃ a ∈ D, a ℓ = true then Classical.choose h else (fun _ => false)
  have hg : ∀ ℓ, (∃ a ∈ D, a ℓ = true) → g ℓ ∈ D ∧ g ℓ ℓ = true := by
    intro ℓ h
    simp only [g, dif_pos h]
    exact Classical.choose_spec h
  have hsub : S.image g ⊆ D := by
    intro b hb
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hb
    exact (hg ℓ (Finset.mem_filter.mp hℓ).2).1
  refine ⟨S.image g, ⟨hsub, ?_⟩, ?_⟩
  · ext ℓ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨g ℓ, Finset.mem_image_of_mem g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), (hg ℓ h).2⟩
    · rintro ⟨b, hb, hbl⟩
      exact ⟨b, hsub hb, hbl⟩
  · calc (S.image g).card ≤ S.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_filter_le _ _
      _ = r := by simp
