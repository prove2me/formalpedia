-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.filter_base_upward_closure
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:04:03.210933+00:00
-- url     : https://prove2.me/submissions/6439a2b2-cc47-4b82-9bb7-30aadaff982c

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [PartialOrder L] [OrderBot L]
    (B : Set L) (hB : IsFilterBase B) :
    IsFilterBase {x : L | ∃ b ∈ B, b ≤ x} := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hB.1
    exact ⟨b, b, hb, le_rfl⟩
  · rintro ⟨b, hb, hb0⟩
    exact hB.2.1 ((le_bot_iff.mp hb0) ▸ hb)
  · rintro x ⟨b, hb, hbx⟩ y ⟨c, hc, hcy⟩
    obtain ⟨d, hd, hdb, hdc⟩ := hB.2.2 b hb c hc
    exact ⟨d, ⟨d, hd, le_rfl⟩, hdb.trans hbx, hdc.trans hcy⟩
