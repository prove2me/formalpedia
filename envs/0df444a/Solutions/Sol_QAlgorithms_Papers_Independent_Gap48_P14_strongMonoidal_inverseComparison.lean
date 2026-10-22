-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.strongMonoidal_inverseComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:50:24.1369+00:00
-- url     : https://prove2.me/submissions/e5be0f48-9cef-47f3-bd84-ed6ecd5b18e3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open Functor.LaxMonoidal Functor.OplaxMonoidal in
theorem g73w_Ftri {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {x y : C} (i : 𝟙_ C ≅ x ⊗ y) (e : y ⊗ x ≅ 𝟙_ C)
    (h : FirstTriangle i e) :
    (ε F ≫ F.map i.hom ≫ δ F x y) ▷ F.obj x ≫ (α_ (F.obj x) (F.obj y) (F.obj x)).hom ≫
      F.obj x ◁ (μ F y x ≫ F.map e.hom ≫ η F) = (λ_ (F.obj x)).hom ≫ (ρ_ (F.obj x)).inv := by
  have hc := congrArg F.map h

  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_leftUnitor,
    Functor.Monoidal.map_rightUnitor_inv, Category.assoc, Functor.Monoidal.μ_δ_assoc] at hc
  have hc2 : F.map i.hom ▷ F.obj x ≫ δ F x y ▷ F.obj x ≫ (α_ (F.obj x) (F.obj y) (F.obj x)).hom ≫
      F.obj x ◁ μ F y x ≫ F.obj x ◁ F.map e.hom =
      η F ▷ F.obj x ≫ (λ_ (F.obj x)).hom ≫ (ρ_ (F.obj x)).inv ≫ F.obj x ◁ ε F := by
    have := μ F (𝟙_ C) x ≫= hc =≫ δ F x (𝟙_ C)
    simpa only [Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id] using this
  calc
    _ = ε F ▷ F.obj x ≫ (F.map i.hom ▷ F.obj x ≫ δ F x y ▷ F.obj x ≫
          (α_ (F.obj x) (F.obj y) (F.obj x)).hom ≫
          F.obj x ◁ μ F y x ≫ F.obj x ◁ F.map e.hom) ≫ F.obj x ◁ η F := by
      simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = _ := by
      rw [hc2]
      simp only [Category.assoc, Functor.Monoidal.whiskerLeft_ε_η, Category.comp_id,
        Functor.Monoidal.whiskerRight_ε_η_assoc]

theorem g73w_whiskerLeft_inj {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    {X Y Y' Y'' : D} (E : Y ⊗ X ≅ 𝟙_ D) (f g : Y' ⟶ Y'') (h : X ◁ f = X ◁ g) : f = g := by
  have h1 : (Y ⊗ X) ◁ f = (Y ⊗ X) ◁ g := by
    rw [tensor_whiskerLeft, tensor_whiskerLeft, h]
  have h3 : E.hom ▷ Y' ≫ 𝟙_ D ◁ f = E.hom ▷ Y' ≫ 𝟙_ D ◁ g := by
    rw [← whisker_exchange, ← whisker_exchange, h1]
  rw [cancel_epi, id_whiskerLeft, id_whiskerLeft] at h3
  simpa using h3

theorem g73w_H1 {D : Type u1} [Category.{v1} D] [MonoidalCategory D] {X Y Y' : D}
    (id' : 𝟙_ D ⟶ X ⊗ Y) (ed : Y ⊗ X ⟶ 𝟙_ D) (I' : 𝟙_ D ⟶ X ⊗ Y')
    (dtri : id' ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ed = (λ_ X).hom ≫ (ρ_ X).inv) :
    id' ≫ X ◁ ((ρ_ Y).inv ≫ Y ◁ I' ≫ (α_ Y X Y').inv ≫ ed ▷ Y' ≫ (λ_ Y').hom) = I' := by
  calc
    _ = 𝟙 _ ⊗≫ (id' ▷ 𝟙_ D ≫ (X ⊗ Y) ◁ I') ⊗≫ X ◁ ed ▷ Y' ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (𝟙_ D ◁ I' ≫ id' ▷ (X ⊗ Y')) ⊗≫ X ◁ ed ▷ Y' ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = I' ⊗≫ (id' ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ed) ▷ Y' ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by
      rw [dtri]; monoidal

theorem g73w_H2 {D : Type u1} [Category.{v1} D] [MonoidalCategory D] {X Y Y' : D}
    (ed : Y ⊗ X ⟶ 𝟙_ D) (I' : 𝟙_ D ⟶ X ⊗ Y') (E' : Y' ⊗ X ⟶ 𝟙_ D)
    (Ftri : I' ▷ X ≫ (α_ X Y' X).hom ≫ X ◁ E' = (λ_ X).hom ≫ (ρ_ X).inv) :
    ((ρ_ Y).inv ≫ Y ◁ I' ≫ (α_ Y X Y').inv ≫ ed ▷ Y' ≫ (λ_ Y').hom) ▷ X ≫ E' = ed := by
  calc
    _ = 𝟙 _ ⊗≫ Y ◁ I' ▷ X ⊗≫ (ed ▷ (Y' ⊗ X) ≫ 𝟙_ D ◁ E') ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ Y ◁ I' ▷ X ⊗≫ ((Y ⊗ X) ◁ E' ≫ ed ▷ 𝟙_ D) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ Y ◁ (I' ▷ X ≫ (α_ X Y' X).hom ≫ X ◁ E') ⊗≫ ed := by
      monoidal
    _ = _ := by
      rw [Ftri]; monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal in
theorem solution
    {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    (hC : ∀ (x y : C) (f : x ⟶ y), IsIso f)
    (hD : ∀ (x y : D) (f : x ⟶ y), IsIso f)
    (c : CoherentInverseData C) (d : CoherentInverseData D)
    (F : C ⥤ D) [F.Monoidal] (x : C) :
    ∃! q : d.inverse (F.obj x) ≅ F.obj (c.inverse x),
      (d.unitIso (F.obj x)).hom ≫ F.obj x ◁ q.hom ≫
          Functor.LaxMonoidal.μ F x (c.inverse x) =
        Functor.LaxMonoidal.ε F ≫ F.map (c.unitIso x).hom ∧
      q.hom ▷ F.obj x ≫ Functor.LaxMonoidal.μ F (c.inverse x) x ≫
          F.map (c.counitIso x).hom =
        (d.counitIso (F.obj x)).hom ≫ Functor.LaxMonoidal.ε F := by
  set X := F.obj x
  set Y := d.inverse X
  set Y' := F.obj (c.inverse x)
  set id' := d.unitIso X
  set ed := d.counitIso X
  let I' : 𝟙_ D ≅ X ⊗ Y' :=
    Functor.Monoidal.εIso F ≪≫ F.mapIso (c.unitIso x) ≪≫
      (Functor.Monoidal.μIso F x (c.inverse x)).symm
  let E' : Y' ⊗ X ≅ 𝟙_ D :=
    Functor.Monoidal.μIso F (c.inverse x) x ≪≫ F.mapIso (c.counitIso x) ≪≫
      (Functor.Monoidal.εIso F).symm
  have hI' : I'.hom = ε F ≫ F.map (c.unitIso x).hom ≫ δ F x (c.inverse x) := rfl
  have hE' : E'.hom = μ F (c.inverse x) x ≫ F.map (c.counitIso x).hom ≫ η F := rfl
  have Ftri : I'.hom ▷ X ≫ (α_ X Y' X).hom ≫ X ◁ E'.hom = (λ_ X).hom ≫ (ρ_ X).inv := by
    rw [hI', hE']
    exact g73w_Ftri F (c.unitIso x) (c.counitIso x) (c.firstTriangle x)
  have dtri : id'.hom ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ed.hom = (λ_ X).hom ≫ (ρ_ X).inv :=
    d.firstTriangle X
  let q : Y ≅ Y' := (ρ_ Y).symm ≪≫ whiskerLeftIso Y I' ≪≫ (α_ Y X Y').symm ≪≫
    whiskerRightIso ed Y' ≪≫ λ_ Y'
  have hq : q.hom = (ρ_ Y).inv ≫ Y ◁ I'.hom ≫ (α_ Y X Y').inv ≫ ed.hom ▷ Y' ≫ (λ_ Y').hom := rfl
  have H1 : id'.hom ≫ X ◁ q.hom = I'.hom := by
    rw [hq]; exact g73w_H1 id'.hom ed.hom I'.hom dtri
  have H2 : q.hom ▷ X ≫ E'.hom = ed.hom := by
    rw [hq]; exact g73w_H2 ed.hom I'.hom E'.hom Ftri
  have H1' : id'.hom ≫ X ◁ q.hom ≫ μ F x (c.inverse x) = ε F ≫ F.map (c.unitIso x).hom := by
    rw [reassoc_of% H1, hI']; simp
  refine ⟨q, ⟨H1', ?_⟩, ?_⟩
  · rw [← H2, hE']; simp [X]
  · rintro q2 ⟨h2, -⟩
    apply Iso.ext
    apply g73w_whiskerLeft_inj ed
    have : id'.hom ≫ X ◁ q2.hom ≫ μ F x (c.inverse x) =
        id'.hom ≫ X ◁ q.hom ≫ μ F x (c.inverse x) := by
      rw [h2, H1']
    rw [cancel_epi] at this
    have h5 := this =≫ δ F x (c.inverse x)
    simp only [Category.assoc, Functor.Monoidal.μ_δ] at h5
    exact (Category.comp_id _).symm.trans (h5.trans (Category.comp_id _))

end Inverses
