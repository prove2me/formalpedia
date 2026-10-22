-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.strongMonoidal_preservesWeakInverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:24:48.295011+00:00
-- url     : https://prove2.me/submissions/c5610f22-4d01-46b2-a201-2e3a6f4cbbc1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem solution
    {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (x y : C) (h : IsWeakInverse x y) :
    IsWeakInverse (F.obj x) (F.obj y) := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := h
  exact ⟨⟨Functor.Monoidal.μIso F x y ≪≫ F.mapIso a ≪≫ (Functor.Monoidal.εIso F).symm⟩,
    ⟨Functor.Monoidal.μIso F y x ≪≫ F.mapIso b ≪≫ (Functor.Monoidal.εIso F).symm⟩⟩

end Inverses
