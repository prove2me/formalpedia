-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_nonmember_has_disjoint_member
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T15:48:09.363168+00:00
-- url     : https://prove2.me/submissions/76390b1a-4291-410b-93be-8adb1508953b

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20


theorem solution {L : Type*} [Lattice L] [BoundedOrder L]
    (B : Set L) (hB : IsQuasipoint B) (a : L) (ha : a ∉ B) :
    ∃ b ∈ B, b ⊓ a = ⊥ := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨b0, hb0⟩ := hB.1.1
  let D : Set L := {x | ∃ b ∈ B, x = b ⊓ a}
  have hD : IsFilterBase D := by
    refine ⟨⟨b0 ⊓ a, b0, hb0, rfl⟩, ?_, ?_⟩
    · rintro ⟨b, hb, he⟩
      exact hn b hb he.symm
    · rintro x ⟨b, hb, hx⟩ y ⟨c, hc, hy⟩
      subst x
      subst y
      obtain ⟨d, hd, hdb, hdc⟩ := hB.1.2.2 b hb c hc
      exact ⟨d ⊓ a, ⟨d, hd, rfl⟩, inf_le_inf_right a hdb, inf_le_inf_right a hdc⟩
  obtain ⟨C, hC, hDC⟩ := filter_base_extends_to_quasipoint D hD
  have hcup := quasipoint_upward_and_meet_closed C hC
  have hBC : B ⊆ C := by
    intro b hb
    exact hcup.1 (b ⊓ a) (hDC ⟨b, hb, rfl⟩) b inf_le_left
  have haC : a ∈ C := hcup.1 (b0 ⊓ a) (hDC ⟨b0, hb0, rfl⟩) a inf_le_right
  have hCB : C = B := hB.2 C hC.1 hBC
  apply ha
  simpa only [hCB] using haC
