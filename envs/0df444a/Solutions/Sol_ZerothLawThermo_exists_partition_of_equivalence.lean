-- Prove2me | solution 1 for ZerothLawThermo.exists_partition_of_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:53.202554+00:00
-- url     : https://prove2.me/submissions/14fa4178-8c6b-4d5f-8ac1-32fafb3ab03a

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution {S : Type*} (TE : S → S → Prop)
    (hTE : Equivalence TE) :
    ∃ P : Set (Set S), Setoid.IsPartition P ∧
      ∀ A B : S, TE A B ↔ ∃ c ∈ P, A ∈ c ∧ B ∈ c := by
  let r : Setoid S := ⟨TE, hTE⟩
  exact ⟨r.classes, r.isPartition_classes, fun _ _ => r.rel_iff_exists_classes⟩
