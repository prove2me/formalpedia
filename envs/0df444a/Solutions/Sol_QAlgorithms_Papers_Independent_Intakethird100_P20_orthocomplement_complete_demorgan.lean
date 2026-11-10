-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.orthocomplement_complete_demorgan
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:55:45.467007+00:00
-- url     : https://prove2.me/submissions/8ab8c35e-a881-458d-a793-9b274ec7b380

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

open QAlgorithms.Papers.Independent.Intakethird100.P20 in
theorem solution {L : Type u} [CompleteLattice L]
    (perp : L → L) (hperp : IsOrthocomplement perp) :
    ∀ s : Set L, perp (sInf s) = sSup (perp '' s) ∧
      perp (sSup s) = sInf (perp '' s) := by
  obtain ⟨-, hdm, hinv⟩ := hperp
  have anti : ∀ a b : L, a ≤ b → perp b ≤ perp a := by
    intro a b hab
    have h := (hdm a b).1
    rw [inf_eq_left.mpr hab] at h
    rw [h]; exact le_sup_right
  intro s
  constructor
  · apply le_antisymm
    · have h1 : perp (sSup (perp '' s)) ≤ sInf s := by
        apply le_sInf
        intro x hx
        have := anti _ _ (le_sSup (mem_image_of_mem perp hx))
        rwa [hinv] at this
      have := anti _ _ h1
      rwa [hinv] at this
    · apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      exact anti _ _ (sInf_le hx)
  · apply le_antisymm
    · apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      exact anti _ _ (le_sSup hx)
    · have h1 : sSup s ≤ perp (sInf (perp '' s)) := by
        apply sSup_le
        intro x hx
        have := anti _ _ (sInf_le (mem_image_of_mem perp hx))
        rwa [hinv] at this
      have := anti _ _ h1
      rwa [hinv] at this
