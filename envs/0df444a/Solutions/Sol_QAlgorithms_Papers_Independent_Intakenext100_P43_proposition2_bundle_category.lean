-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P43.proposition2_bundle_category
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:38:05.469439+00:00
-- url     : https://prove2.me/submissions/cefe9da6-35fc-4984-96aa-2cf0bfd38d78

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

open QAlgorithms.Papers.Independent.Intakenext100.P43 in
theorem solution (B : C) :
    ∃ cat : Category (Over B), cat.toCategoryStruct = bundleCategoryStruct B := by
  refine ⟨{ toCategoryStruct := bundleCategoryStruct B
            id_comp := fun f => ?_
            comp_id := fun f => ?_
            assoc := fun f g h => ?_ }, rfl⟩
  · apply Over.OverMorphism.ext
    exact Category.id_comp _
  · apply Over.OverMorphism.ext
    exact Category.comp_id _
  · apply Over.OverMorphism.ext
    exact Category.assoc _ _ _

end Ordinary
