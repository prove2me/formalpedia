-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.stoneBasic_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:09:18.203682+00:00
-- url     : https://prove2.me/submissions/beb33304-5af4-46de-aea2-fd42e85d1bde

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

open QAlgorithms.Papers.Independent.Intakethird100.P20


theorem solution {L : Type*} [Lattice L] [BoundedOrder L] (a : L) :
    (stoneBasic a).Nonempty ↔ a ≠ ⊥ := by
  classical
  constructor
  · rintro ⟨B, hb⟩ hz
    exact B.property.1.2.1 (hz ▸ hb)
  · intro ha
    have hbase : IsFilterBase ({a} : Set L) := by
      refine ⟨⟨a, rfl⟩, ?_, ?_⟩
      · intro hz
        exact ha (show a = ⊥ from (Set.mem_singleton_iff.mp hz).symm)
      · intro x hx y hy
        have hx' : x = a := hx
        have hy' : y = a := hy
        subst x
        subst y
        exact ⟨a, rfl, le_rfl, le_rfl⟩
    obtain ⟨B, hB, hsub⟩ := filter_base_extends_to_quasipoint {a} hbase
    exact ⟨⟨B, hB⟩, hsub (Set.mem_singleton a)⟩
