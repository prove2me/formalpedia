-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P02.functorialInverse_double
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:36:40.993022+00:00
-- url     : https://prove2.me/submissions/1fa7b7db-eb45-4482-9777-d68f7ee3e245

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P02
open QAlgorithms.Papers.Independent.Gap48.P02
open CategoryTheory MonoidalCategory

universe v u

section g73i
variable {M : Type u} [Category.{v} M] [MonoidalCategory M]

def g73i_rightIso {w v : M} (e : w ⊗ v ≅ 𝟙_ M) : tensorRight w ⋙ tensorRight v ≅ 𝟭 M :=
  (tensorRightTensor w v).symm ≪≫
    NatIso.ofComponents (F := tensorRight (w ⊗ v)) (G := tensorRight (𝟙_ M))
      (fun X => whiskerLeftIso X e) (by intros; exact (whisker_exchange _ _).symm) ≪≫
    rightUnitorNatIso M

def g73i_leftIso {w u : M} (e : u ⊗ w ≅ 𝟙_ M) : tensorLeft w ⋙ tensorLeft u ≅ 𝟭 M :=
  (tensorLeftTensor u w).symm ≪≫
    NatIso.ofComponents (F := tensorLeft (u ⊗ w)) (G := tensorLeft (𝟙_ M))
      (fun X => whiskerRightIso e X) (by intros; exact (whisker_exchange _ _)) ≪≫
    leftUnitorNatIso M

theorem g73i_nat (c : FunctorialInverseChoice M) {x y : M} (f : x ⟶ y) :
    (f ⊗ₘ c.inverse.map f) ≫ c.evaluation.hom.app y = c.evaluation.hom.app x := by
  have := c.evaluation.hom.naturality f
  exact this.trans (Category.comp_id _)

instance g73i_isIso (c : FunctorialInverseChoice M) {x y : M} (f : x ⟶ y) :
    IsIso (f ⊗ₘ c.inverse.map f) := by
  have : (f ⊗ₘ c.inverse.map f) = c.evaluation.hom.app x ≫ c.evaluation.inv.app y := by
    exact (Iso.eq_comp_inv (c.evaluation.app y)).mpr (g73i_nat c f)
  rw [this]; exact Iso.isIso_hom (c.evaluation.app x ≪≫ (c.evaluation.app y).symm)

def g73i_dd (c : FunctorialInverseChoice M) (x : M) : x ≅ c.inverse.obj (c.inverse.obj x) :=
  (ρ_ x).symm ≪≫ whiskerLeftIso x (c.evaluation.app (c.inverse.obj x)).symm ≪≫
    (α_ x _ _).symm ≪≫ whiskerRightIso (c.evaluation.app x) _ ≪≫ λ_ _

theorem g73i_both (c : FunctorialInverseChoice M) (x : M) :
    (∃ v, Nonempty (x ⊗ v ≅ 𝟙_ M)) ∧ (∃ u, Nonempty (u ⊗ x ≅ 𝟙_ M)) :=
  ⟨⟨_, ⟨c.evaluation.app x⟩⟩,
   ⟨c.inverse.obj x, ⟨whiskerLeftIso _ (g73i_dd c x) ≪≫ c.evaluation.app (c.inverse.obj x)⟩⟩⟩

theorem g73i_rightFF (c : FunctorialInverseChoice M) (w : M) :
    (tensorRight w).Full ∧ (tensorRight w).Faithful := by
  have hF : ∀ w : M, (tensorRight w).Faithful := by
    intro w
    obtain ⟨v, ⟨e⟩⟩ := (g73i_both c w).1
    have : (tensorRight w ⋙ tensorRight v).Faithful := Functor.Faithful.of_iso (g73i_rightIso e).symm
    exact Functor.Faithful.of_comp _ (tensorRight v)
  refine ⟨?_, hF w⟩
  obtain ⟨v, ⟨e⟩⟩ := (g73i_both c w).1
  have : (tensorRight w ⋙ tensorRight v).Full := Functor.Full.of_iso (g73i_rightIso e).symm
  have := hF v
  exact Functor.Full.of_comp_faithful _ (tensorRight v)

theorem g73i_leftFF (c : FunctorialInverseChoice M) (w : M) :
    (tensorLeft w).Full ∧ (tensorLeft w).Faithful := by
  have hF : ∀ w : M, (tensorLeft w).Faithful := by
    intro w
    obtain ⟨u, ⟨e⟩⟩ := (g73i_both c w).2
    have : (tensorLeft w ⋙ tensorLeft u).Faithful := Functor.Faithful.of_iso (g73i_leftIso e).symm
    exact Functor.Faithful.of_comp _ (tensorLeft u)
  refine ⟨?_, hF w⟩
  obtain ⟨u, ⟨e⟩⟩ := (g73i_both c w).2
  have : (tensorLeft w ⋙ tensorLeft u).Full := Functor.Full.of_iso (g73i_leftIso e).symm
  have := hF u
  exact Functor.Full.of_comp_faithful _ (tensorLeft u)

theorem g73i_groupoid (c : FunctorialInverseChoice M) : IsGroupoid M := by
  constructor
  intro x y f
  have hfac := (tensorHom_def f (c.inverse.map f))
  have hfac' := (tensorHom_def' f (c.inverse.map f))
  -- retraction of f ▷ i x
  obtain ⟨hFu1, hFa1⟩ := g73i_rightFF c (c.inverse.obj x)
  obtain ⟨hFu2, hFa2⟩ := g73i_rightFF c (c.inverse.obj y)
  let r : y ⊗ c.inverse.obj x ⟶ x ⊗ c.inverse.obj x :=
    (y ◁ c.inverse.map f) ≫ inv (f ⊗ₘ c.inverse.map f)
  have hr : f ▷ c.inverse.obj x ≫ r = 𝟙 _ := by
    simp only [r, ← Category.assoc, ← hfac, IsIso.hom_inv_id]
  let s : y ⊗ c.inverse.obj y ⟶ x ⊗ c.inverse.obj y :=
    inv (f ⊗ₘ c.inverse.map f) ≫ (x ◁ c.inverse.map f)
  have hs : s ≫ f ▷ c.inverse.obj y = 𝟙 _ := by
    simp only [s, Category.assoc, ← hfac', IsIso.inv_hom_id]
  obtain ⟨r', hr'⟩ := (tensorRight (c.inverse.obj x)).map_surjective r
  obtain ⟨s', hs'⟩ := (tensorRight (c.inverse.obj y)).map_surjective s
  have h1 : f ≫ r' = 𝟙 x := by
    apply (tensorRight (c.inverse.obj x)).map_injective
    rw [CategoryTheory.Functor.map_comp, hr', CategoryTheory.Functor.map_id]; exact hr
  have h2 : s' ≫ f = 𝟙 y := by
    apply (tensorRight (c.inverse.obj y)).map_injective
    rw [CategoryTheory.Functor.map_comp, hs', CategoryTheory.Functor.map_id]; exact hs
  have h3 : r' = s' := by
    calc r' = (s' ≫ f) ≫ r' := by rw [h2, Category.id_comp]
      _ = s' := by rw [Category.assoc, h1, Category.comp_id]
  exact ⟨⟨r', h1, h3 ▸ h2⟩⟩

end g73i

section g73i2
variable {M : Type u} [Category.{v} M] [MonoidalCategory M]

def g73i_E (c : FunctorialInverseChoice M) (x : M) : x ⊗ c.inverse.obj x ≅ 𝟙_ M :=
  c.evaluation.app x

theorem g73i_nat_inv (c : FunctorialInverseChoice M) {x y : M} (f : x ⟶ y) :
    (g73i_E c y).inv = (g73i_E c x).inv ≫ (f ⊗ₘ c.inverse.map f) :=
  ((Iso.eq_inv_comp (c.evaluation.app x)).mpr
    ((Iso.eq_comp_inv (c.evaluation.app y)).mpr (g73i_nat c f)).symm)

theorem g73i_nat' (c : FunctorialInverseChoice M) {x y : M} (f : x ⟶ y) :
    (g73i_E c x).hom = (f ⊗ₘ c.inverse.map f) ≫ (g73i_E c y).hom :=
  (g73i_nat c f).symm

def g73i_dd' (c : FunctorialInverseChoice M) (x : M) : x ≅ c.inverse.obj (c.inverse.obj x) :=
  (ρ_ x).symm ≪≫ whiskerLeftIso x (g73i_E c (c.inverse.obj x)).symm ≪≫
    (α_ x _ _).symm ≪≫ whiskerRightIso (g73i_E c x) _ ≪≫ λ_ _

theorem g73i_dd_nat (c : FunctorialInverseChoice M) {x y : M} (f : x ⟶ y) :
    f ≫ (g73i_dd' c y).hom = (g73i_dd' c x).hom ≫ c.inverse.map (c.inverse.map f) := by
  simp only [g73i_dd', Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
  rw [g73i_nat_inv c (c.inverse.map f), g73i_nat' c f]
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc f (g73i_E c (c.inverse.obj x)).inv,
    ← leftUnitor_naturality (c.inverse.map (c.inverse.map f)),
    ← whisker_exchange_assoc (g73i_E c y).hom (c.inverse.map (c.inverse.map f))]
  monoidal

end g73i2

/-- Lemma 51, PDF p. 20: every chosen functorial inverse has its
square naturally isomorphic to the identity endofunctor. -/
theorem solution
    (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (choice : FunctorialInverseChoice M) :
    Nonempty (choice.inverse ⋙ choice.inverse ≅ 𝟭 M) :=
  ⟨(NatIso.ofComponents (F := 𝟭 M) (G := choice.inverse ⋙ choice.inverse)
    (fun x => g73i_dd' choice x) (fun f => g73i_dd_nat choice f)).symm⟩
