-- Prove2me | solution 1 for TwoCategory.smallBasedCategory_exists_isWeakTwoPullback_fibered
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:32:23.227496+00:00
-- url     : https://prove2.me/submissions/8e75f728-b67e-41e8-a44a-59ea610c216d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits QAlgorithms.Papers.Independent.Intakenext100.P43

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback_fibered

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


section fibered

/-- Conjugating a strongly cartesian morphism by isomorphisms lying over identities gives a
strongly cartesian morphism. -/
lemma isStronglyCartesian_conj {𝒜 : Type*} [Category 𝒜] (p : 𝒜 ⥤ 𝒮) {R S : 𝒮} (f : R ⟶ S)
    {a b a' b' : 𝒜} (φ : a ⟶ b) (hφ : p.IsStronglyCartesian f φ) (i : a' ≅ a)
    (hi : p.IsHomLift (𝟙 R) i.hom) (j : b ≅ b') (hj : p.IsHomLift (𝟙 S) j.hom) :
    p.IsStronglyCartesian f (i.hom ≫ φ ≫ j.hom) := by
  have : p.IsStronglyCartesian (𝟙 S) j.hom := inferInstance
  have : p.IsStronglyCartesian (𝟙 R) i.hom := inferInstance
  have : p.IsStronglyCartesian (f ≫ 𝟙 S) (φ ≫ j.hom) := inferInstance
  have h : p.IsStronglyCartesian (𝟙 R ≫ f ≫ 𝟙 S) (i.hom ≫ φ ≫ j.hom) := inferInstance
  rwa [Category.id_comp, Category.comp_id] at h

lemma isStronglyCartesian_iso_comp {𝒜 : Type*} [Category 𝒜] (p : 𝒜 ⥤ 𝒮) {R S : 𝒮} (f : R ⟶ S)
    {a b a' : 𝒜} (φ : a ⟶ b) (hφ : p.IsStronglyCartesian f φ) (i : a' ≅ a)
    (hi : p.IsHomLift (𝟙 R) i.hom) :
    p.IsStronglyCartesian f (i.hom ≫ φ) := by
  have : p.IsStronglyCartesian (𝟙 R) i.hom := inferInstance
  have h : p.IsStronglyCartesian (𝟙 R ≫ f) (i.hom ≫ φ) := inferInstance
  rwa [Category.id_comp] at h

variable {F G}

lemma P_isHomLift_iff {R S : 𝒮} {X Y : PCat F G} (f : R ⟶ S) (φ : X ⟶ Y) :
    (P F G).p.IsHomLift f φ ↔ 𝒳.p.IsHomLift f φ.hom.fst :=
  (BasedFunctor.isHomLift_iff (first F G) f φ).symm

lemma P_isHomLift_iff_snd {R S : 𝒮} {X Y : PCat F G} (f : R ⟶ S) (φ : X ⟶ Y) :
    (P F G).p.IsHomLift f φ ↔ 𝒴.p.IsHomLift f φ.hom.snd :=
  (BasedFunctor.isHomLift_iff (second F G) f φ).symm

/-- A morphism of the 2-fibre product whose two components are strongly cartesian is strongly
cartesian. -/
lemma isStronglyCartesian_of_fst_snd
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ))
    {R S : 𝒮} (f : R ⟶ S) {X Y : PCat F G} (φ : X ⟶ Y)
    [(P F G).p.IsHomLift f φ]
    (h1 : 𝒳.p.IsStronglyCartesian f φ.hom.fst) (h2 : 𝒴.p.IsStronglyCartesian f φ.hom.snd) :
    (P F G).p.IsStronglyCartesian f φ := by
  have hG' := hG f φ.hom.snd h2
  constructor
  intro Z g ψ hψ
  have hψ1 : 𝒳.p.IsHomLift (g ≫ f) ψ.hom.fst := (P_isHomLift_iff _ _).1 hψ
  have hψ2 : 𝒴.p.IsHomLift (g ≫ f) ψ.hom.snd := (P_isHomLift_iff_snd _ _).1 hψ
  obtain ⟨c, ⟨hc, hcφ⟩, hcu⟩ :=
    IsStronglyCartesian.universal_property 𝒳.p f φ.hom.fst g (g ≫ f) rfl ψ.hom.fst
  obtain ⟨d, ⟨hd, hdφ⟩, hdu⟩ :=
    IsStronglyCartesian.universal_property 𝒴.p f φ.hom.snd g (g ≫ f) rfl ψ.hom.snd
  have w : F.map c ≫ X.obj.iso.hom = Z.obj.iso.hom ≫ G.map d := by
    have hX : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj X.obj.fst)) X.obj.iso.hom := X.property
    have hZ : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj Z.obj.fst)) Z.obj.iso.hom := Z.property
    have : 𝒵.p.IsHomLift g (F.map c) := inferInstance
    have : 𝒵.p.IsHomLift g (G.map d) := inferInstance
    have l1 : 𝒵.p.IsHomLift g (F.map c ≫ X.obj.iso.hom) :=
      IsHomLift.comp_lift_id_right' 𝒵.p g (F.map c) (𝒳.p.obj X.obj.fst) X.obj.iso.hom
    have l2 : 𝒵.p.IsHomLift g (Z.obj.iso.hom ≫ G.map d) :=
      IsHomLift.comp_lift_id_left' 𝒵.p (𝒳.p.obj Z.obj.fst) Z.obj.iso.hom g (G.map d)
    apply IsStronglyCartesian.ext 𝒵.p f (G.map φ.hom.snd) g
    rw [Category.assoc, Category.assoc, ← φ.hom.w, ← Functor.map_comp_assoc, ← Functor.map_comp,
      hcφ, hdφ]
    exact ψ.hom.w
  refine ⟨ObjectProperty.homMk ⟨c, d, w⟩, ⟨(P_isHomLift_iff _ _).2 hc, ?_⟩, ?_⟩
  · apply ObjectProperty.hom_ext
    apply CategoricalPullback.hom_ext
    · exact hcφ
    · exact hdφ
  · rintro π ⟨hπ, hπφ⟩
    apply ObjectProperty.hom_ext
    apply CategoricalPullback.hom_ext
    · exact hcu _ ⟨(P_isHomLift_iff _ _).1 hπ, congrArg (fun t => t.hom.fst) hπφ⟩
    · exact hdu _ ⟨(P_isHomLift_iff_snd _ _).1 hπ, congrArg (fun t => t.hom.snd) hπφ⟩


/-- Strongly cartesian lifts in the 2-fibre product, with strongly cartesian components. -/
lemma exists_lift (h𝒳 : 𝒳.p.IsFibered) (h𝒴 : 𝒴.p.IsFibered)
    (hF : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ : a ⟶ b),
      𝒳.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (F.map φ))
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ))
    (Y : PCat F G) {R S : 𝒮} (hS : 𝒳.p.obj Y.obj.fst = S) (f : R ⟶ S) :
    ∃ (X : PCat F G) (φ : X ⟶ Y), (P F G).p.IsStronglyCartesian f φ ∧
      𝒳.p.IsStronglyCartesian f φ.hom.fst ∧ 𝒴.p.IsStronglyCartesian f φ.hom.snd := by
  subst hS
  obtain ⟨x, a, ha⟩ := IsPreFibered.exists_isCartesian 𝒳.p (a := Y.obj.fst) rfl f
  obtain ⟨y, b, hb⟩ := IsPreFibered.exists_isCartesian 𝒴.p (a := Y.obj.snd)
    (snd_obj F G Y) f
  have ha' : 𝒳.p.IsStronglyCartesian f a := inferInstance
  have hb' : 𝒴.p.IsStronglyCartesian f b := inferInstance
  have hFa := hF f a ha'
  have hGb := hG f b hb'
  have hyx : 𝒴.p.obj y = R := IsHomLift.domain_eq 𝒴.p f b
  obtain rfl : 𝒳.p.obj x = R := IsHomLift.domain_eq 𝒳.p f a
  have hY : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj Y.obj.fst)) Y.obj.iso.hom := Y.property
  have l1 : 𝒵.p.IsHomLift f (F.map a ≫ Y.obj.iso.hom) :=
    IsHomLift.comp_lift_id_right' 𝒵.p f (F.map a) (𝒳.p.obj Y.obj.fst) Y.obj.iso.hom
  have l2 : 𝒵.p.IsHomLift f (G.map b ≫ Y.obj.iso.inv) :=
    IsHomLift.comp_lift_id_right' 𝒵.p f (G.map b) (𝒳.p.obj Y.obj.fst) Y.obj.iso.inv
  obtain ⟨u, ⟨hu, huφ⟩, -⟩ := IsStronglyCartesian.universal_property 𝒵.p f (G.map b)
    (𝟙 _) f (Category.id_comp f).symm (F.map a ≫ Y.obj.iso.hom)
  obtain ⟨v, ⟨hv, hvφ⟩, -⟩ := IsStronglyCartesian.universal_property 𝒵.p f (F.map a)
    (𝟙 _) f (Category.id_comp f).symm (G.map b ≫ Y.obj.iso.inv)
  have huv : u ≫ v = 𝟙 _ := by
    have : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj x)) (u ≫ v) := inferInstance
    apply IsStronglyCartesian.ext 𝒵.p f (F.map a) (𝟙 (𝒳.p.obj x))
    rw [Category.assoc, hvφ, ← Category.assoc, huφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  have huv' : v ≫ u = 𝟙 _ := by
    have : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj x)) (v ≫ u) := inferInstance
    have : 𝒵.p.IsHomLift (𝟙 (𝒳.p.obj x)) (𝟙 (G.obj y)) :=
      IsHomLift.id ((BasedFunctor.w_obj G y).trans hyx)
    apply IsStronglyCartesian.ext 𝒵.p f (G.map b) (𝟙 (𝒳.p.obj x))
    rw [Category.assoc, huφ, ← Category.assoc, hvφ, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  let e : F.obj x ≅ G.obj y := ⟨u, v, huv, huv'⟩
  let X : PCat F G := ⟨⟨x, y, e⟩, hu⟩
  let φ : X ⟶ Y := ObjectProperty.homMk ⟨a, b, huφ.symm⟩
  have hφ : (P F G).p.IsHomLift f φ := (P_isHomLift_iff (X := X) (Y := Y) f φ).2 ha'.toIsHomLift
  exact ⟨X, φ, isStronglyCartesian_of_fst_snd hG f φ ha' hb', ha', hb'⟩

lemma P_isFibered (h𝒳 : 𝒳.p.IsFibered) (h𝒴 : 𝒴.p.IsFibered)
    (hF : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ : a ⟶ b),
      𝒳.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (F.map φ))
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ)) :
    (P F G).p.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian (fun Y R f => by
    obtain ⟨X, φ, h, -, -⟩ := exists_lift h𝒳 h𝒴 hF hG Y rfl f
    exact ⟨X, φ, h⟩)

/-- The two projections preserve strongly cartesian morphisms. -/
lemma proj_isStronglyCartesian (h𝒳 : 𝒳.p.IsFibered) (h𝒴 : 𝒴.p.IsFibered)
    (hF : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ : a ⟶ b),
      𝒳.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (F.map φ))
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ))
    {R S : 𝒮} (f : R ⟶ S) {X Y : PCat F G} (φ : X ⟶ Y)
    (hφ : (P F G).p.IsStronglyCartesian f φ) :
    𝒳.p.IsStronglyCartesian f φ.hom.fst ∧ 𝒴.p.IsStronglyCartesian f φ.hom.snd := by
  have hφ' : (P F G).p.IsHomLift f φ := hφ.toIsHomLift
  obtain ⟨X₀, φ₀, h₀, h₀1, h₀2⟩ :=
    exists_lift h𝒳 h𝒴 hF hG Y (IsHomLift.codomain_eq (P F G).p f φ) f
  have h₀c : (P F G).p.IsCartesian f φ₀ :=
    @IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ (P F G).p _ _ _ _ f φ₀ h₀
  have hφc : (P F G).p.IsCartesian f φ :=
    @IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ (P F G).p _ _ _ _ f φ hφ
  let i := IsCartesian.domainUniqueUpToIso (P F G).p f φ₀ φ
  have hi : (P F G).p.IsHomLift (𝟙 R) i.hom := IsCartesian.map_isHomLift (P F G).p f φ₀ φ
  have hiφ : i.hom ≫ φ₀ = φ := IsCartesian.fac (P F G).p f φ₀ φ
  have hi1 : 𝒳.p.IsHomLift (𝟙 R) ((first F G).mapIso i).hom :=
    (P_isHomLift_iff (X := X) (Y := X₀) _ i.hom).1 hi
  have hi2 : 𝒴.p.IsHomLift (𝟙 R) ((second F G).mapIso i).hom :=
    (P_isHomLift_iff_snd (X := X) (Y := X₀) _ i.hom).1 hi
  have e1 : φ.hom.fst = ((first F G).mapIso i).hom ≫ φ₀.hom.fst := by
    rw [← hiφ]; rfl
  have e2 : φ.hom.snd = ((second F G).mapIso i).hom ≫ φ₀.hom.snd := by
    rw [← hiφ]; rfl
  constructor
  · rw [e1]; exact isStronglyCartesian_iso_comp 𝒳.p f φ₀.hom.fst h₀1 _ hi1
  · rw [e2]; exact isStronglyCartesian_iso_comp 𝒴.p f φ₀.hom.snd h₀2 _ hi2

/-- A cone morphism out of a cone whose legs preserve strongly cartesian morphisms preserves
strongly cartesian morphisms. -/
lemma coneMorphism_isStronglyCartesian
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ))
    (Q : TwoPullbackCone F G)
    (hQ1 : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
      Q.vertex.p.IsStronglyCartesian f φ → 𝒳.p.IsStronglyCartesian f (Q.first.map φ))
    (hQ2 : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
      Q.vertex.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (Q.second.map φ))
    (k : TwoConeMorphism Q (cone F G)) {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b)
    (hφ : Q.vertex.p.IsStronglyCartesian f φ) :
    (P F G).p.IsStronglyCartesian f (k.map.map φ) := by
  have hk : (P F G).p.IsHomLift f (k.map.map φ) := BasedFunctor.preserves_isHomLift k.map f φ
  have ha : Q.vertex.p.obj a = R := IsHomLift.domain_eq Q.vertex.p f φ
  have hb : Q.vertex.p.obj b = S := IsHomLift.codomain_eq Q.vertex.p f φ
  let c1 := (BasedNatTrans.forgetful _ _).mapIso k.firstCell
  let c2 := (BasedNatTrans.forgetful _ _).mapIso k.secondCell
  have h1 := hQ1 f φ hφ
  have h2 := hQ2 f φ hφ
  have i1 : 𝒳.p.IsHomLift (𝟙 R) (c1.app a).symm.hom := k.firstCell.inv.isHomLift ha
  have j1 : 𝒳.p.IsHomLift (𝟙 S) (c1.app b).hom := k.firstCell.hom.isHomLift hb
  have i2 : 𝒴.p.IsHomLift (𝟙 R) (c2.app a).symm.hom := k.secondCell.inv.isHomLift ha
  have j2 : 𝒴.p.IsHomLift (𝟙 S) (c2.app b).hom := k.secondCell.hom.isHomLift hb
  have n1 : Q.first.map φ ≫ (c1.app b).hom = (c1.app a).hom ≫ (k.map.map φ).hom.fst :=
    c1.hom.naturality φ
  have e1 : (k.map.map φ).hom.fst = (c1.app a).symm.hom ≫ Q.first.map φ ≫ (c1.app b).hom := by
    exact (Iso.eq_inv_comp _).2 n1.symm
  have n2 : Q.second.map φ ≫ (c2.app b).hom = (c2.app a).hom ≫ (k.map.map φ).hom.snd :=
    c2.hom.naturality φ
  have e2 : (k.map.map φ).hom.snd = (c2.app a).symm.hom ≫ Q.second.map φ ≫ (c2.app b).hom := by
    exact (Iso.eq_inv_comp _).2 n2.symm
  apply isStronglyCartesian_of_fst_snd hG f (k.map.map φ)
  · rw [e1]; exact isStronglyCartesian_conj 𝒳.p f (Q.first.map φ) h1 _ i1 _ j1
  · rw [e2]; exact isStronglyCartesian_conj 𝒴.p f (Q.second.map φ) h2 _ i2 _ j2

end fibered

end Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback_fibered

open Sol_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback_fibered in
theorem solution
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝒳 𝒴 𝒵 : BasedCategory.{v₂, v₂} 𝒮)
    (h𝒳 : 𝒳.p.IsFibered) (h𝒴 : 𝒴.p.IsFibered) (h𝒵 : 𝒵.p.IsFibered)
    (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵)
    (hF : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ : a ⟶ b),
      𝒳.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (F.map φ))
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ)) :
    ∃ P : TwoPullbackCone F G, IsWeakTwoPullback P ∧ P.vertex.p.IsFibered ∧
      (∀ {R S : 𝒮} (f : R ⟶ S) {a b : P.vertex.obj} (φ : a ⟶ b),
        P.vertex.p.IsStronglyCartesian f φ → 𝒳.p.IsStronglyCartesian f (P.first.map φ)) ∧
      (∀ {R S : 𝒮} (f : R ⟶ S) {a b : P.vertex.obj} (φ : a ⟶ b),
        P.vertex.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (P.second.map φ)) ∧
      ∀ (Q : TwoPullbackCone F G), Q.vertex.p.IsFibered →
        (∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ → 𝒳.p.IsStronglyCartesian f (Q.first.map φ)) →
        (∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (Q.second.map φ)) →
        ∀ (k : TwoConeMorphism Q P) {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ →
            P.vertex.p.IsStronglyCartesian f (k.map.map φ) :=
  ⟨cone F G, isWeak F G, P_isFibered h𝒳 h𝒴 hF hG,
    fun {_ _} f {_ _} φ hφ => (proj_isStronglyCartesian h𝒳 h𝒴 hF hG f φ hφ).1,
    fun {_ _} f {_ _} φ hφ => (proj_isStronglyCartesian h𝒳 h𝒴 hF hG f φ hφ).2,
    fun Q _ hQ1 hQ2 k {_ _} f {_ _} φ hφ =>
      coneMorphism_isStronglyCartesian hG Q hQ1 hQ2 k f φ hφ⟩
