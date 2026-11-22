-- Prove2me | solution 1 for TopGroupoid.SetGroupoid.exists_groupoid_hom_equiv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:35:37.341713+00:00
-- url     : https://prove2.me/submissions/25db8dda-aca9-444b-9845-3926df1c41a2

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open CategoryTheory

set_option autoImplicit false

universe u v

open TopGroupoid

theorem solution {X : Type u} {R : Type v} (G : SetGroupoid X R) :
    ∃ (_ : Groupoid.{v} X) (φ : ∀ x y : X, (x ⟶ y) ≃ {g : R // G.src g = x ∧ G.tgt g = y}),
      (∀ x : X, (φ x x (𝟙 x) : R) = G.unit x) ∧
      (∀ (x y z : X) (f : x ⟶ y) (g : y ⟶ z),
        (φ x z (f ≫ g) : R) =
          G.comp ⟨((φ y z g : R), (φ x y f : R)), (φ y z g).2.1.trans (φ x y f).2.2.symm⟩) ∧
      ∀ (x y : X) (f : x ⟶ y), (φ y x (Groupoid.inv f) : R) = G.inv (φ x y f) := by
  let inst : Groupoid.{v} X :=
    { Hom := fun x y => {g : R // G.src g = x ∧ G.tgt g = y}
      id := fun x => ⟨G.unit x, G.src_unit x, G.tgt_unit x⟩
      comp := fun {x y z} f g => ⟨G.comp ⟨(g.1, f.1), g.2.1.trans f.2.2.symm⟩, by
          rw [G.src_comp, G.tgt_comp]; exact ⟨f.2.1, g.2.2⟩⟩
      id_comp := by
        rintro x y ⟨g, rfl, rfl⟩
        exact Subtype.ext (G.comp_unit g)
      comp_id := by
        rintro x y ⟨g, rfl, rfl⟩
        exact Subtype.ext (G.unit_comp g)
      assoc := by
        rintro w x y z ⟨f, rfl, hf⟩ ⟨g, hg, hg'⟩ ⟨h, hh, rfl⟩
        exact Subtype.ext (G.comp_assoc h g f (hh.trans hg'.symm) (hg.trans hf.symm))
      inv := fun {x y} f => ⟨G.inv f.1, by rw [G.src_inv, G.tgt_inv]; exact ⟨f.2.2, f.2.1⟩⟩
      inv_comp := by
        rintro x y ⟨g, rfl, rfl⟩
        exact Subtype.ext (G.comp_inv g)
      comp_inv := by
        rintro x y ⟨g, rfl, rfl⟩
        exact Subtype.ext (G.inv_comp g) }
  exact ⟨inst, fun x y => Equiv.refl _, fun x => rfl, fun x y z f g => rfl, fun x y f => rfl⟩
