-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P43.proposition3_regular_right_action
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:32:57.511299+00:00
-- url     : https://prove2.me/submissions/0e0133fc-abb2-4c60-812a-6a5d5e6b4777

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

open QAlgorithms.Papers.Independent.Intakenext100.P43 in
theorem solution {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] :
    IsRightAction G G (MonObj.mul (X := G)) :=
  ⟨fun _ a x y => MonObj.lift_lift_assoc a x y,
    fun T a => MonObj.lift_comp_one_right a (toUnit T)⟩
