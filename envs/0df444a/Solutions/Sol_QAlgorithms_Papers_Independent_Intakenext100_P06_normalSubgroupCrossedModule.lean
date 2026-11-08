-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P06.normalSubgroupCrossedModule
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:10:58.638201+00:00
-- url     : https://prove2.me/submissions/4132ff87-50ba-41ff-8855-f392ba0c2d74

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

open QAlgorithms.Papers.Independent.Intakenext100.P06 in
theorem solution {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal] :
    IsCrossedModule H.subtype (MulAut.conjNormal : G →* MulAut H) := by
  refine ⟨fun g h => ?_, fun h k => ?_⟩
  · simp
  · apply Subtype.ext
    simp
