-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:26:52.000346+00:00
-- url     : https://prove2.me/submissions/6a76484f-a91d-4b30-8fd9-77bc1b0f4a90

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P09 in
theorem solution :
    (∀ (G : Type u) (V : Type v) [Group G] [AddCommGroup V] [DistribMulAction G V],
      ∀ n : ℕ,
      Cohomology (equivariantCochains G (X := G) (V := V)) n =
        Cohomology (groupCochains G V) n) ∧
    (∀ (G : Type u) (V : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
      [DistribMulAction G V] [ContinuousSMul G V], ∀ n : ℕ,
      Cohomology (continuousEquivariant G (X := G) (V := V)) n =
        Cohomology (fun k => continuousCochains k ⊓ groupCochains G V k) n) := by
  refine ⟨fun G V _ _ _ n => ?_, fun G V _ _ _ _ _ _ _ _ n => ?_⟩
  · have h : (fun k => equivariantCochains G (X := G) (V := V) k) = groupCochains G V := by
      funext k
      ext f
      exact Iff.rfl
    exact congrArg (fun S => Cohomology S n) h
  · have h : (fun k => continuousEquivariant G (X := G) (V := V) k) =
        (fun k => continuousCochains k ⊓ groupCochains G V k) := by
      funext k
      ext f
      exact Iff.rfl
    exact congrArg (fun S => Cohomology S n) h
