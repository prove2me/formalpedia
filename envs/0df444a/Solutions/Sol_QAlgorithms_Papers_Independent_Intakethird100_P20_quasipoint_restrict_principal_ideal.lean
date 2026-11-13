-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_restrict_principal_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:08:47.451313+00:00
-- url     : https://prove2.me/submissions/789c022e-fb63-4b03-9aa4-5254b38a758c

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_upward_closure
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [Lattice L] [BoundedOrder L]
    (a : L) (B : StoneSpectrum L) (hBa : a ∈ B.val) :
    letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
    IsQuasipoint {b : Set.Iic a | b.val ∈ B.val} := by
  classical
  letI : Bot (Set.Iic a) := ⟨⟨⊥, bot_le⟩⟩
  let R : Set (Set.Iic a) := {b | b.val ∈ B.val}
  change IsQuasipoint R
  have hR : IsFilterBase R := by
    refine ⟨⟨⟨a, le_rfl⟩, hBa⟩, B.property.1.2.1, ?_⟩
    intro x hx y hy
    obtain ⟨z, hz, hzx, hzy⟩ := B.property.1.2.2 x.val hx y.val hy
    exact ⟨⟨z, hzx.trans x.property⟩, hz, hzx, hzy⟩
  refine ⟨hR, ?_⟩
  intro C hC hRC
  let S : Set L := Subtype.val '' C
  have hS : IsFilterBase S := by
    refine ⟨hC.1.image _, ?_, ?_⟩
    · rintro ⟨c, hc, hc0⟩
      have heq : c = (⊥ : Set.Iic a) := Subtype.ext hc0
      exact hC.2.1 (heq ▸ hc)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx, hzy⟩ := hC.2.2 x hx y hy
      exact ⟨z.val, ⟨z, hz, rfl⟩, hzx, hzy⟩
  let D : Set L := {b | ∃ c ∈ S, c ≤ b}
  have hD : IsFilterBase D := filter_base_upward_closure S hS
  have hBD : B.val ⊆ D := by
    intro b hb
    have hab := (quasipoint_upward_and_meet_closed B.val B.property).2 a hBa b hb
    exact ⟨a ⊓ b, ⟨⟨a ⊓ b, inf_le_left⟩, hRC hab, rfl⟩, inf_le_right⟩
  have heq := B.property.2 D hD hBD
  apply Set.Subset.antisymm _ hRC
  intro c hc
  have hDc : c.val ∈ D := ⟨c.val, ⟨c, hc, rfl⟩, le_rfl⟩
  rw [heq] at hDc
  exact hDc
