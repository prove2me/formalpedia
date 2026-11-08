-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P59.ordinaryEquivalence_iff_quasiInverse
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:20:39.080896+00:00
-- url     : https://prove2.me/submissions/841fd439-4a73-4fc1-b707-137f5d925beb

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

open CategoryTheory

universe u v uC vC uD vD uE vE

open QAlgorithms.Papers.Independent.Intake100.P59 in
theorem solution
    {A : Type uC} {B : Type uD} [Category.{vC} A] [Category.{vD} B]
    (F : A ⥤ B) :
    (F.Full ∧ F.Faithful ∧ F.EssSurj) ↔
      ∃ G : B ⥤ A, Nonempty (F ⋙ G ≅ 𝟭 A) ∧ Nonempty (G ⋙ F ≅ 𝟭 B) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    haveI : F.IsEquivalence := { faithful := h2, full := h1, essSurj := h3 }
    exact ⟨F.inv, ⟨F.asEquivalence.unitIso.symm⟩, ⟨F.asEquivalence.counitIso⟩⟩
  · rintro ⟨G, ⟨η⟩, ⟨ε⟩⟩
    haveI : F.IsEquivalence := Functor.IsEquivalence.mk' G η.symm ε
    exact ⟨inferInstance, inferInstance, inferInstance⟩
