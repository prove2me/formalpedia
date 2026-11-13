-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_extend_principal_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:13:44.319206+00:00
-- url     : https://prove2.me/submissions/a294ca02-0a51-453a-8fef-aa063229655a

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_upward_closure
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [PartialOrder L] [OrderBot L]
    (a : L) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    ∀ C : StoneSpectrum (Set.Iic a), IsQuasipoint {b : L | ∃ c ∈ C.val, c.val ≤ b} := by
  classical
  letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
  intro C
  let D : Set L := {b | ∃ c ∈ C.val, c.val ≤ b}
  change IsQuasipoint D
  let S : Set L := Subtype.val '' C.val
  have hS : IsFilterBase S := by
    refine ⟨C.property.1.1.image _, ?_, ?_⟩
    · rintro ⟨c, hc, hc0⟩
      have heq : c = (⊥ : Set.Iic a) := Subtype.ext hc0
      exact C.property.1.2.1 (heq ▸ hc)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx, hzy⟩ := C.property.1.2.2 x hx y hy
      exact ⟨z.val, ⟨z, hz, rfl⟩, hzx, hzy⟩
  have hD : IsFilterBase D := by
    have heq : D = {b : L | ∃ x ∈ S, x ≤ b} := by
      ext b
      constructor
      · rintro ⟨c, hc, hcb⟩; exact ⟨c.val, ⟨c, hc, rfl⟩, hcb⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, hcb⟩; exact ⟨c, hc, hcb⟩
    rw [heq]
    exact filter_base_upward_closure S hS
  refine ⟨hD, ?_⟩
  intro E hE hDE
  have haD : a ∈ D := by
    obtain ⟨c, hc⟩ := C.property.1.1
    exact ⟨c, hc, c.property⟩
  have haE := hDE haD
  let R : Set (Set.Iic a) := {c | c.val ∈ E}
  have hR : IsFilterBase R := by
    refine ⟨⟨⟨a, le_rfl⟩, haE⟩, hE.2.1, ?_⟩
    intro x hx y hy
    obtain ⟨z, hz, hzx, hzy⟩ := hE.2.2 x.val hx y.val hy
    exact ⟨⟨z, hzx.trans x.property⟩, hz, hzx, hzy⟩
  have hCR : C.val ⊆ R := fun c hc => hDE ⟨c, hc, le_rfl⟩
  have hRC := C.property.2 R hR hCR
  apply Set.Subset.antisymm _ hDE
  intro x hx
  obtain ⟨d, hd, hda, hdx⟩ := hE.2.2 a haE x hx
  have hRd : (⟨d, hda⟩ : Set.Iic a) ∈ R := hd
  rw [hRC] at hRd
  exact ⟨⟨d, hda⟩, hRd, hdx⟩
