-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P43.proposition1_pullbacks_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:21:12.926119+00:00
-- url     : https://prove2.me/submissions/5f885ae0-cc66-4119-8ac6-a3805facea22

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

theorem solution {C : Type u} [Category.{v} C]
    {X Y Z P Q : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p1 : P ⟶ X) (p2 : P ⟶ Y) (q1 : Q ⟶ X) (q2 : Q ⟶ Y)
    (hp : IsPullback p1 p2 f g) (hq : IsPullback q1 q2 f g) :
    Nonempty (P ≅ Q) :=
  ⟨hp.isoIsPullback _ _ hq⟩
