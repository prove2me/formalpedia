-- Prove2me | solution 1 for TwoCategory.smallBasedCategory_exists_isWeakTwoPullback
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:30:15.74515+00:00
-- url     : https://prove2.me/submissions/7990a060-e0ce-402e-ba4f-1902596dfd13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits QAlgorithms.Papers.Independent.Intakenext100.P43

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback

open CategoryTheory.Functor CategoricalPullback

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 𝒴 𝒵 : BasedCategory.{v₂, max u₂ v₂} 𝒮} (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵)

/-- Objects of the categorical pullback whose structural isomorphism is vertical. -/
def vert : ObjectProperty (F.toFunctor ⊡ G.toFunctor) :=
  fun X => 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj X.fst)) X.iso.hom

/-- The underlying category of the 2-fibre product. -/
abbrev PCat := (vert F G).FullSubcategory

instance (X : PCat F G) : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj X.obj.fst)) X.obj.iso.hom := X.property

/-- The 2-fibre product as a based category. -/
def P : BasedCategory.{v₂, max u₂ v₂} 𝒮 where
  obj := PCat F G
  p := (vert F G).ι ⋙ π₁ _ _ ⋙ 𝒳.p

lemma snd_obj (X : PCat F G) : 𝒴.p.obj X.obj.snd = 𝒳.p.obj X.obj.fst := by
  rw [← BasedFunctor.w_obj G X.obj.snd]
  exact IsHomLift.codomain_eq 𝒵.p (𝟙 (𝒳.p.obj X.obj.fst)) X.obj.iso.hom

lemma snd_lift {X Y : PCat F G} (f : X ⟶ Y) :
    𝒴.p.IsHomLift (𝒳.p.map f.hom.fst) f.hom.snd := by
  have h1 : 𝒵.p.IsHomLift (𝒳.p.map f.hom.fst) (F.map f.hom.fst ≫ Y.obj.iso.hom) :=
    inferInstance
  rw [f.hom.w] at h1
  have h2 : 𝒵.p.IsHomLift (𝒳.p.map f.hom.fst)
      (X.obj.iso.inv ≫ X.obj.iso.hom ≫ G.map f.hom.snd) := inferInstance
  simp only [Iso.inv_hom_id_assoc] at h2
  exact BasedFunctor.isHomLift_map G _ _

/-- First projection. -/
def first : P F G ⥤ᵇ 𝒳 where
  toFunctor := (vert F G).ι ⋙ π₁ _ _
  w := rfl

/-- Second projection. -/
def second : P F G ⥤ᵇ 𝒴 where
  toFunctor := (vert F G).ι ⋙ π₂ _ _
  w := CategoryTheory.Functor.ext (fun X => snd_obj F G X)
    (fun X Y f => by
      have := snd_lift F G f
      exact IsHomLift.fac' 𝒴.p (𝒳.p.map f.hom.fst) f.hom.snd)


/-- The comparison 2-isomorphism of the 2-fibre product. -/
def comparison : (first F G ≫ F : P F G ⟶ 𝒵) ≅ second F G ≫ G :=
  BasedNatIso.mkNatIso (NatIso.ofComponents (fun X => X.obj.iso) (fun f => f.hom.w))
    (fun X => X.property)

/-- The 2-fibre product cone. -/
def cone : TwoPullbackCone F G where
  vertex := P F G
  first := first F G
  second := second F G
  comparison := comparison F G

lemma aux {D : Type*} [Category D] {X Y Z W : D} (ψ : X ⟶ W) (p : X ⟶ Y) (i : Y ⟶ Z) (q : Z ⟶ W)
    (q' : W ⟶ Z) (h : ψ = p ≫ 𝟙 _ ≫ i ≫ 𝟙 _ ≫ q) (hq : q ≫ q' = 𝟙 _) : p ≫ i = ψ ≫ q' := by
  subst h; simp [hq]

lemma aux0 {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) :
    f = 𝟙 X ≫ 𝟙 X ≫ f ≫ 𝟙 Y ≫ 𝟙 Y := by
  simp

section lift

variable {F G} (Q : TwoPullbackCone F G)

/-- The underlying natural isomorphism of the comparison cell of a cone. -/
def ψ : (Q.first ≫ F).toFunctor ≅ (Q.second ≫ G).toFunctor :=
  (BasedNatTrans.forgetful _ _).mapIso Q.comparison

/-- The canonical based functor from the vertex of a cone to the 2-fibre product. -/
def lift : Q.vertex ⥤ᵇ P F G where
  toFunctor :=
    { obj := fun w => ⟨⟨Q.first.obj w, Q.second.obj w, (ψ Q).app w⟩,
        Q.comparison.hom.isHomLift (BasedFunctor.w_obj Q.first w).symm⟩
      map := fun {_ _} f => ObjectProperty.homMk ⟨Q.first.map f, Q.second.map f,
        (ψ Q).hom.naturality f⟩
      map_id := fun x => ObjectProperty.hom_ext _
        (CategoricalPullback.hom_ext (Q.first.map_id x) (Q.second.map_id x))
      map_comp := fun f g => ObjectProperty.hom_ext _
        (CategoricalPullback.hom_ext (Q.first.map_comp f g) (Q.second.map_comp f g)) }
  w := Q.first.w

/-- The canonical cone morphism from a cone to the 2-fibre product cone. -/
def liftMor : TwoConeMorphism Q (cone F G) where
  map := lift Q
  firstCell := Iso.refl _
  secondCell := Iso.refl _
  coherence := by
    apply BasedNatTrans.homCategory.ext
    ext x
    change Q.comparison.hom.toNatTrans.app x =
      F.map (𝟙 (Q.first.obj x)) ≫ 𝟙 (F.obj (Q.first.obj x)) ≫
        Q.comparison.hom.toNatTrans.app x ≫ 𝟙 (G.obj (Q.second.obj x)) ≫
          G.map (𝟙 (Q.second.obj x))
    rw [F.map_id, G.map_id]
    exact aux0 _

end lift

theorem isWeak : IsWeakTwoPullback (cone F G) := by
  intro Q
  refine ⟨liftMor Q, fun u' => ?_⟩
  let a' := (BasedNatTrans.forgetful _ _).mapIso u'.firstCell
  let b' := (BasedNatTrans.forgetful _ _).mapIso u'.secondCell
  have hcoh : ∀ x, F.map (a'.hom.app x) ≫ (u'.map.obj x).obj.iso.hom =
      ((ψ Q).app x).hom ≫ G.map (b'.hom.app x) := by
    intro x
    have h := congrArg (fun t => t.toNatTrans.app x) u'.coherence
    change (ψ Q).hom.app x = F.map (a'.hom.app x) ≫ 𝟙 _ ≫ (u'.map.obj x).obj.iso.hom ≫ 𝟙 _ ≫
      G.map (b'.inv.app x) at h
    exact aux _ _ _ _ _ h ((G.map_comp _ _).symm.trans
      ((congrArg G.map (b'.inv_hom_id_app x)).trans (G.map_id _)))
  let ν0 : (lift Q).toFunctor ≅ u'.map.toFunctor :=
    NatIso.ofComponents
      (fun x => ObjectProperty.isoMk _ (CategoricalPullback.mkIso (a'.app x) (b'.app x) (hcoh x)))
      (by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply CategoricalPullback.hom_ext
        · exact a'.hom.naturality f
        · exact b'.hom.naturality f)
  let ν : lift Q ≅ u'.map := BasedNatIso.mkNatIso ν0 (fun x => by
    have : 𝒳.p.IsHomLift (𝟙 (Q.vertex.p.obj x)) ((first F G).map (ν0.hom.app x)) :=
      u'.firstCell.hom.isHomLift' x
    exact BasedFunctor.isHomLift_map (first F G) _ _)
  refine ⟨ν, ⟨?_, ?_⟩, ?_⟩
  · apply BasedNatTrans.homCategory.ext
    ext x
    change 𝟙 _ ≫ a'.hom.app x = a'.hom.app x
    simp
  · apply BasedNatTrans.homCategory.ext
    ext x
    change 𝟙 _ ≫ b'.hom.app x = b'.hom.app x
    simp
  · rintro ν' ⟨h1, h2⟩
    apply Iso.ext
    apply BasedNatTrans.homCategory.ext
    ext x
    apply ObjectProperty.hom_ext
    apply CategoricalPullback.hom_ext
    · have h := congrArg (fun t => t.toNatTrans.app x) h1
      change 𝟙 _ ≫ (ν'.hom.toNatTrans.app x).hom.fst = a'.hom.app x at h
      change (ν'.hom.toNatTrans.app x).hom.fst = a'.hom.app x
      exact (Category.id_comp _).symm.trans h
    · have h := congrArg (fun t => t.toNatTrans.app x) h2
      change 𝟙 _ ≫ (ν'.hom.toNatTrans.app x).hom.snd = b'.hom.app x at h
      change (ν'.hom.toNatTrans.app x).hom.snd = b'.hom.app x
      exact (Category.id_comp _).symm.trans h

end Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback

open Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback in
theorem solution
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝒳 𝒴 𝒵 : BasedCategory.{v₂, v₂} 𝒮) (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵) :
    ∃ P : TwoPullbackCone F G, IsWeakTwoPullback P :=
  ⟨cone F G, isWeak F G⟩
