-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.baire_of_locally_compact_or_complete
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:01:00.906306+00:00
-- url     : https://prove2.me/submissions/92b97eac-b71b-44ad-b12d-5158e93f7e97

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

theorem solution :
    (∀ (M : Type u) [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M], BaireSpace M) ∧
    (∀ (M : Type u) [MetricSpace M] [CompleteSpace M], BaireSpace M) :=
  ⟨fun _ _ _ _ => inferInstance, fun _ _ _ => inferInstance⟩

end
