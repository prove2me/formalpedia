-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:30:01.010362+00:00
-- url     : https://prove2.me/submissions/b97c75e1-9ce7-449e-8351-74816464def3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P09 in
theorem solution {G : Type u} {V : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [DistribMulAction G V] [ContinuousSMul G V]
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (C : OpenCover G) (hC : C.sets = translatedFamily U) :
    ∀ n : ℕ, (coverCochains (V := V) C n ⊓ equivariantCochains G n) =
      coverCochains C n ⊓ groupCochains G V n := by
  intro n
  rfl
