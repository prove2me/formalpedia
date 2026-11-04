-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.normalInclusionCrossedModule
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:25:57.959311+00:00
-- url     : https://prove2.me/submissions/584d2902-8f87-46e0-a561-e3da1867d38c

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

open QAlgorithms.Papers.Independent.Intake100.P20
universe u

/-- Inclusion of a normal subgroup satisfies both crossed-module axioms for conjugation. -/
theorem solution {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] :
    CrossedModule N.subtype (MulAut.conjNormal : G →* MulAut N) := by
  constructor
  · intro g c
    rfl
  · intro c d
    apply Subtype.ext
    rfl

#print axioms solution


