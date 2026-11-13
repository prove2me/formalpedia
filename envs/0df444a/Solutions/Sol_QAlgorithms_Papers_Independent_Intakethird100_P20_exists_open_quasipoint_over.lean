-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.exists_open_quasipoint_over
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:33:36.086229+00:00
-- url     : https://prove2.me/submissions/6a773042-6bd2-4c62-bac6-76540fa187c2

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_cluster_characterization
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type*} [TopologicalSpace M] [T2Space M]
    (x : M) : ∃ B : StoneSpectrum (Opens M), LiesOver B x := by
  classical
  let N : Set (Opens M) := {U | x ∈ (U : Set M)}
  have hN : IsFilterBase N := by
    refine ⟨⟨⊤, Set.mem_univ x⟩, ?_, ?_⟩
    · intro h; exact h
    · intro U hU V hV
      exact ⟨U ⊓ V, ⟨hU, hV⟩, inf_le_left, inf_le_right⟩
  obtain ⟨P, hP, hNP⟩ := filter_base_extends_to_quasipoint N hN
  refine ⟨⟨P, hP⟩, ?_⟩
  apply (open_quasipoint_cluster_characterization ⟨P, hP⟩ x).2.mpr
  intro U hxU
  exact hNP hxU
