-- Prove2me | solution 1 for TopStack.Inertia.proj_fiberedInGroupoids
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:37:59.60351+00:00
-- url     : https://prove2.me/submissions/6bb6a0b9-3d10-4220-8e96-9ce13da1954f

import Mathlib
import Definitions.Def_TopStack_Inertia

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

theorem solution {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
    (hp : p.IsFibered) (hfib : ∀ S : 𝒮, IsGroupoid (p.Fiber S)) :
    (TopStack.Inertia.proj p).IsFibered ∧
      ∀ S : 𝒮, IsGroupoid ((TopStack.Inertia.proj p).Fiber S) := by
  -- (1) A morphism of `𝒳` lying over an identity is an isomorphism.
  have hiso : ∀ {S : 𝒮} {a b : 𝒳} (φ : a ⟶ b) [p.IsHomLift (𝟙 S) φ], IsIso φ := by
    intro S a b φ _
    have h1 : IsIso (Functor.Fiber.homMk p S φ) := (hfib S).all_isIso _
    have h2 := Functor.map_isIso (Functor.Fiber.fiberInclusion (p := p) (S := S))
      (Functor.Fiber.homMk p S φ)
    simpa using h2
  -- (2) A morphism of the inertia lifts `f` along `proj p` iff its underlying morphism lifts `f`
  -- along `p`.
  have hT : ∀ {R S : 𝒮} {A₁ A₂ : TopStack.Inertia p} (f : R ⟶ S) (Φ : A₁ ⟶ A₂),
      (TopStack.Inertia.proj p).IsHomLift f Φ ↔ p.IsHomLift f Φ.1 := by
    intro R S A₁ A₂ f Φ
    constructor
    · intro h
      have ha := CategoryTheory.IsHomLift.domain_eq (TopStack.Inertia.proj p) f Φ
      have hb := CategoryTheory.IsHomLift.codomain_eq (TopStack.Inertia.proj p) f Φ
      have hf := CategoryTheory.IsHomLift.fac (TopStack.Inertia.proj p) f Φ
      exact CategoryTheory.IsHomLift.of_fac p f Φ.1 ha hb hf
    · intro h
      have ha := CategoryTheory.IsHomLift.domain_eq p f Φ.1
      have hb := CategoryTheory.IsHomLift.codomain_eq p f Φ.1
      have hf := CategoryTheory.IsHomLift.fac p f Φ.1
      exact CategoryTheory.IsHomLift.of_fac (TopStack.Inertia.proj p) f Φ ha hb hf
  -- (3) The automorphism of an object of the inertia lies over an identity.
  have haut : ∀ A : TopStack.Inertia p, p.IsHomLift (𝟙 (p.obj A.obj)) A.aut.hom := by
    intro A
    have h := CategoryTheory.IsHomLift.map p A.aut.hom
    rw [A.map_aut_hom] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- `proj p` admits strongly Cartesian lifts.
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro A R g
    obtain ⟨y, ψ, hψ⟩ :=
      CategoryTheory.IsPreFibered.exists_isCartesian p
        (rfl : p.obj A.obj = (TopStack.Inertia.proj p).obj A) g
    have : p.IsStronglyCartesian g ψ :=
      @Functor.IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ p hp _ _ g _ _ ψ hψ
    have := haut A
    have : p.IsHomLift g (ψ ≫ A.aut.hom) :=
      CategoryTheory.IsHomLift.comp_lift_id_right' p g ψ (p.obj A.obj) A.aut.hom
    -- the pulled-back automorphism `β` of `y`
    let β : y ⟶ y := Functor.IsStronglyCartesian.map p g ψ (g := 𝟙 R)
      (Category.id_comp g).symm (ψ ≫ A.aut.hom)
    have hβlift : p.IsHomLift (𝟙 R) β := Functor.IsStronglyCartesian.map_isHomLift p g ψ _ _
    have hβfac : β ≫ ψ = ψ ≫ A.aut.hom := Functor.IsStronglyCartesian.fac p g ψ _ _
    have : IsIso β := hiso (S := R) β
    have hβid : p.map β = 𝟙 (p.obj y) := by
      have h := CategoryTheory.IsHomLift.fac' p (𝟙 R) β
      simpa using h
    let B : TopStack.Inertia p := ⟨y, asIso β, hβid⟩
    let Ψ : B ⟶ A := ⟨ψ, hβfac⟩
    have hΨ : (TopStack.Inertia.proj p).IsHomLift g Ψ := (hT g Ψ).2 inferInstance
    refine ⟨B, Ψ, ?_⟩
    refine { universal_property' := ?_ }
    intro C h Φ' hΦ'
    have : p.IsHomLift (h ≫ g) Φ'.1 := (hT _ Φ').1 hΦ'
    let χ₀ : C.obj ⟶ y := Functor.IsStronglyCartesian.map p g ψ (g := h) rfl Φ'.1
    have hχ₀lift : p.IsHomLift h χ₀ := Functor.IsStronglyCartesian.map_isHomLift p g ψ _ _
    have hχ₀ : χ₀ ≫ ψ = Φ'.1 := Functor.IsStronglyCartesian.fac p g ψ _ _
    have := haut C
    have hcond : C.aut.hom ≫ χ₀ = χ₀ ≫ β := by
      have : p.IsHomLift h (C.aut.hom ≫ χ₀) :=
        CategoryTheory.IsHomLift.comp_lift_id_left' p (p.obj C.obj) C.aut.hom h χ₀
      have : p.IsHomLift h (χ₀ ≫ β) :=
        CategoryTheory.IsHomLift.comp_lift_id_right' p h χ₀ R β
      apply Functor.IsStronglyCartesian.ext p g ψ h
      rw [Category.assoc, hχ₀, Category.assoc, hβfac, ← Category.assoc, hχ₀]
      exact Φ'.2
    let χ : C ⟶ B := ⟨χ₀, hcond⟩
    refine ⟨χ, ⟨(hT h χ).2 hχ₀lift, Subtype.ext hχ₀⟩, ?_⟩
    rintro χ' ⟨hχ'lift, hχ'fac⟩
    have : p.IsHomLift h χ'.1 := (hT h χ').1 hχ'lift
    apply Subtype.ext
    exact Functor.IsStronglyCartesian.map_uniq p g ψ rfl Φ'.1 χ'.1 (congrArg Subtype.val hχ'fac)
  · -- The fibres of `proj p` are groupoids.
    intro S
    refine ⟨fun {X Y} Φ => ?_⟩
    have : p.IsHomLift (𝟙 S) Φ.1.1 := (hT _ Φ.1).1 Φ.2
    have : IsIso Φ.1.1 := hiso (S := S) Φ.1.1
    have hcond : Y.1.aut.hom ≫ inv Φ.1.1 = inv Φ.1.1 ≫ X.1.aut.hom := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, ← Φ.1.2, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    let ι₀ : Y.1 ⟶ X.1 := ⟨inv Φ.1.1, hcond⟩
    have : (TopStack.Inertia.proj p).IsHomLift (𝟙 S) ι₀ := (hT _ ι₀).2 inferInstance
    let ι : Y ⟶ X := ⟨ι₀, inferInstance⟩
    exact ⟨⟨ι, Subtype.ext (Subtype.ext (IsIso.hom_inv_id _)),
      Subtype.ext (Subtype.ext (IsIso.inv_hom_id _))⟩⟩
