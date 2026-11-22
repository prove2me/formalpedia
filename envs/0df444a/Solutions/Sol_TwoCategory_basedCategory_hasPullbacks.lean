-- Prove2me | solution 1 for TwoCategory.basedCategory_hasPullbacks
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:27:42.083353+00:00
-- url     : https://prove2.me/submissions/43a95ab7-d6a3-42a0-b8a9-8a42deab2a9a

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace Sol_TwoCategory_basedCategory_hasPullbacks

open Limits

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Two based functors are equal as soon as their underlying functors are. -/
theorem bext {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮} {F G : BasedFunctor 𝒳 𝒴}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F; cases G; cases h; rfl

section

variable {𝒳 𝒴 𝒵 : BasedCategory.{v₂, u₂} 𝒮} (F : BasedFunctor 𝒳 𝒵) (G : BasedFunctor 𝒴 𝒵)

/-- Objects of the strict fibre product: pairs `(x, y)` with `F x = G y`. -/
@[ext]
structure PObj : Type u₂ where
  /-- first component -/
  x : 𝒳.obj
  /-- second component -/
  y : 𝒴.obj
  /-- compatibility -/
  h : F.obj x = G.obj y

variable {F G}

/-- Morphisms of the strict fibre product: pairs `(a, b)` with `F a = G b`
(up to the canonical identifications of the endpoints). -/
@[ext]
structure PHom (a b : PObj F G) : Type v₂ where
  fst : a.x ⟶ b.x
  snd : a.y ⟶ b.y
  w : F.map fst ≫ eqToHom b.h = eqToHom a.h ≫ G.map snd

/-- Identity morphisms. -/
def PHom.id (a : PObj F G) : PHom a a where
  fst := 𝟙 _
  snd := 𝟙 _
  w := by simp

/-- Composition of morphisms. -/
def PHom.comp {a b c : PObj F G} (f : PHom a b) (g : PHom b c) : PHom a c where
  fst := f.fst ≫ g.fst
  snd := f.snd ≫ g.snd
  w := by
    rw [Functor.map_comp, Category.assoc, g.w, ← Category.assoc, f.w, Category.assoc,
      Functor.map_comp]

instance : Category (PObj F G) where
  Hom := PHom
  id := PHom.id
  comp := PHom.comp
  id_comp _ := PHom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := PHom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := PHom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

@[simp] lemma id_fst (a : PObj F G) : (𝟙 a : PHom a a).fst = 𝟙 a.x := rfl
@[simp] lemma id_snd (a : PObj F G) : (𝟙 a : PHom a a).snd = 𝟙 a.y := rfl
@[simp] lemma comp_fst {a b c : PObj F G} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : PHom a c).fst = (f : PHom a b).fst ≫ (g : PHom b c).fst := rfl
@[simp] lemma comp_snd {a b c : PObj F G} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g : PHom a c).snd = (f : PHom a b).snd ≫ (g : PHom b c).snd := rfl

@[simp] lemma eqToHom_fst {a b : PObj F G} (h : a = b) :
    (eqToHom h : PHom a b).fst = eqToHom (by rw [h]) := by
  subst h; rfl
@[simp] lemma eqToHom_snd {a b : PObj F G} (h : a = b) :
    (eqToHom h : PHom a b).snd = eqToHom (by rw [h]) := by
  subst h; rfl

variable (F G)

/-- First projection. -/
@[simps]
def π₁ : PObj F G ⥤ 𝒳.obj where
  obj a := a.x
  map f := (f : PHom _ _).fst

/-- Second projection. -/
@[simps]
def π₂ : PObj F G ⥤ 𝒴.obj where
  obj a := a.y
  map f := (f : PHom _ _).snd

/-- The square of underlying functors commutes strictly. -/
theorem comm : π₁ F G ⋙ F.toFunctor = π₂ F G ⋙ G.toFunctor := by
  refine CategoryTheory.Functor.ext (fun a => a.h) (fun a b f => ?_)
  have hw := congrArg (· ≫ eqToHom b.h.symm) (f : PHom a b).w
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hw
  exact hw

/-- The strict fibre product as a based category, projecting to the base through `𝒳`. -/
def P : BasedCategory.{v₂, u₂} 𝒮 where
  obj := PObj F G
  p := π₁ F G ⋙ F.toFunctor ⋙ 𝒵.p

/-- The first projection as a based functor. -/
def fstB : P F G ⟶ 𝒳 where
  toFunctor := π₁ F G
  w := by
    show π₁ F G ⋙ 𝒳.p = π₁ F G ⋙ F.toFunctor ⋙ 𝒵.p
    rw [F.w]

/-- The second projection as a based functor. -/
def sndB : P F G ⟶ 𝒴 where
  toFunctor := π₂ F G
  w := by
    show π₂ F G ⋙ 𝒴.p = π₁ F G ⋙ F.toFunctor ⋙ 𝒵.p
    rw [← G.w, ← Functor.assoc, ← Functor.assoc, comm F G]

theorem condition : fstB F G ≫ F = sndB F G ≫ G := bext (comm F G)

variable {F G}

/-- The induced functor into the strict fibre product. -/
def liftFunctor {W : Type*} [Category W] (c : W ⥤ 𝒳.obj) (d : W ⥤ 𝒴.obj)
    (h : c ⋙ F.toFunctor = d ⋙ G.toFunctor) : W ⥤ PObj F G where
  obj w := ⟨c.obj w, d.obj w, Functor.congr_obj h w⟩
  map {w w'} f :=
    ({ fst := c.map f
       snd := d.map f
       w := by
         have hf := Functor.congr_hom h f
         simp only [Functor.comp_map] at hf
         simp [hf] } : PHom _ _)
  map_id w := PHom.ext (c.map_id w) (d.map_id w)
  map_comp f g := PHom.ext (c.map_comp f g) (d.map_comp f g)

/-- Functors into the strict fibre product are determined by their two projections. -/
theorem functor_ext {W : Type*} [Category W] {m m' : W ⥤ PObj F G}
    (h₁ : m ⋙ π₁ F G = m' ⋙ π₁ F G) (h₂ : m ⋙ π₂ F G = m' ⋙ π₂ F G) : m = m' := by
  refine CategoryTheory.Functor.ext (fun w => PObj.ext (Functor.congr_obj h₁ w)
    (Functor.congr_obj h₂ w)) (fun a b f => PHom.ext ?_ ?_)
  · have hf := Functor.congr_hom h₁ f
    simp only [Functor.comp_map, π₁_map] at hf
    rw [comp_fst, comp_fst, eqToHom_fst, eqToHom_fst, hf]
    rfl
  · have hf := Functor.congr_hom h₂ f
    simp only [Functor.comp_map, π₂_map] at hf
    rw [comp_snd, comp_snd, eqToHom_snd, eqToHom_snd, hf]
    rfl

variable (F G)

/-- The pullback cone given by the strict fibre product is a limit cone. -/
def isLimit : IsLimit (PullbackCone.mk (fstB F G) (sndB F G) (condition F G)) := by
  refine PullbackCone.IsLimit.mk (condition F G)
    (fun s => ⟨liftFunctor s.fst.toFunctor s.snd.toFunctor
      (congrArg BasedFunctor.toFunctor s.condition), ?_⟩) (fun s => bext rfl) (fun s => bext rfl)
    (fun s m h₁ h₂ => bext (functor_ext (congrArg BasedFunctor.toFunctor h₁)
      (congrArg BasedFunctor.toFunctor h₂)))
  show s.fst.toFunctor ⋙ F.toFunctor ⋙ 𝒵.p = s.pt.p
  rw [F.w, s.fst.w]

end

end Sol_TwoCategory_basedCategory_hasPullbacks

open Sol_TwoCategory_basedCategory_hasPullbacks in
theorem solution {𝒮 : Type u₁} [Category.{v₁} 𝒮] :
    Limits.HasPullbacks (BasedCategory.{v₂, u₂} 𝒮) := by
  have : ∀ {X Y Z : BasedCategory.{v₂, u₂} 𝒮} {f : X ⟶ Z} {g : Y ⟶ Z},
      Limits.HasLimit (Limits.cospan f g) := fun {_ _ _ f g} =>
    Limits.HasLimit.mk ⟨_, isLimit f g⟩
  exact Limits.hasPullbacks_of_hasLimit_cospan _
