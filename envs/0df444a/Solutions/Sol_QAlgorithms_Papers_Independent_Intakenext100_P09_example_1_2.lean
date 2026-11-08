-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:32:04.284421+00:00
-- url     : https://prove2.me/submissions/c32b8b87-142a-47f2-93e8-f69fe3b199b2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P09 in
theorem solution :
    (∀ (G : Type u) (V : Type v) [Group G] [AddCommGroup V] [DistribMulAction G V],
      ∀ n : ℕ, equivariantCochains G (X := G) (V := V) n = groupCochains G V n) ∧
    (∀ (G : Type u) (V : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
      [DistribMulAction G V] [ContinuousSMul G V], ∀ n : ℕ,
      continuousEquivariant G (X := G) (V := V) n =
        continuousCochains n ⊓ groupCochains G V n) := by
  refine ⟨?_, ?_⟩ <;> intros <;> rfl
