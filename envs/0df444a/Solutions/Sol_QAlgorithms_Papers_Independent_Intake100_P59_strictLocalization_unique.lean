-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P59.strictLocalization_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:57:04.907754+00:00
-- url     : https://prove2.me/submissions/8bd9c849-6022-432d-8adb-0bef656f4bb5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

open CategoryTheory

universe u v uC vC uD vD uE vE

open QAlgorithms.Papers.Independent.Intake100.P59 in
theorem solution
    {C D D2 : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} D2]
    (W : MorphismProperty C) (L : C ⥤ D) (L2 : C ⥤ D2)
    (hL : ∀ (E : Type u) [Category.{v} E],
      Nonempty (Localization.StrictUniversalPropertyFixedTarget L W E))
    (hL2 : ∀ (E : Type u) [Category.{v} E],
      Nonempty (Localization.StrictUniversalPropertyFixedTarget L2 W E)) :
    ∃! F : D ⥤ D2, L ⋙ F = L2 ∧
      ∃ G : D2 ⥤ D, L2 ⋙ G = L ∧ F ⋙ G = 𝟭 D ∧ G ⋙ F = 𝟭 D2 := by
  obtain ⟨u⟩ := hL D2
  obtain ⟨u2⟩ := hL2 D
  obtain ⟨uD⟩ := hL D
  obtain ⟨u2D2⟩ := hL2 D2
  refine ⟨u.lift L2 u2.inverts, ⟨u.fac L2 u2.inverts, u2.lift L u.inverts,
    u2.fac L u.inverts, ?_, ?_⟩, ?_⟩
  · apply uD.uniq
    rw [← Functor.assoc, u.fac, u2.fac, Functor.comp_id]
  · apply u2D2.uniq
    rw [← Functor.assoc, u2.fac, u.fac, Functor.comp_id]
  · rintro F' ⟨hF', -⟩
    apply u.uniq
    rw [hF', u.fac]
