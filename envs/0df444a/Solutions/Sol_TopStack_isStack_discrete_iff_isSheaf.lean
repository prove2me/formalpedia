-- Prove2me | solution 1 for TopStack.isStack_discrete_iff_isSheaf
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:48:59.78641+00:00
-- url     : https://prove2.me/submissions/5d879836-a37d-4bab-a380-69f8702d135f

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TopStackAux

open Opposite

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)

abbrev F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w} := (P ⋙ typeToCat.{w}).toPseudofunctor'

lemma hom_eq {S : C} {M N : (F P).obj (.mk (op S))}
    (a b : M ⟶ N) : a = b :=
  @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom (α := P.obj (op S)) M N) a b

lemma as_eq {S : C} {M N : (F P).obj (.mk (op S))}
    (a : M ⟶ N) : M.as = N.as :=
  Discrete.eq_of_hom (α := P.obj (op S)) a

def homOfEq {S : C} {M N : (F P).obj (.mk (op S))}
    (h : M.as = N.as) : M ⟶ N :=
  Discrete.eqToHom (α := P.obj (op S)) h

def isoOfEq {S : C} {M N : (F P).obj (.mk (op S))}
    (h : M.as = N.as) : M ≅ N :=
  Discrete.eqToIso (α := P.obj (op S)) h

variable {P}

def descentDataOfCompatible {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (x : ∀ i, P.obj (op (X i))) (hx : Presieve.Arrows.Compatible P f x) :
    (F P).DescentData f where
  obj i := Discrete.mk (x i)
  hom Y q i₁ i₂ f₁ f₂ h₁ h₂ := homOfEq P (hx i₁ i₂ Y f₁ f₂ (h₁.trans h₂.symm))
  pullHom_hom := by intros; apply hom_eq
  hom_self := by intros; apply hom_eq
  hom_comp := by intros; apply hom_eq

theorem key {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) :
    ((F P).toDescentData f).IsEquivalence ↔ Presieve.IsSheafFor P (Presieve.ofArrows X f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  constructor
  · intro hG x hx
    obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty (((F P).toDescentData f).obj M ≅
        descentDataOfCompatible f x hx) :=
      ⟨_, ⟨((F P).toDescentData f).objObjPreimageIso _⟩⟩
    refine ⟨M.as, fun i => as_eq P (e.hom.hom i), fun t ht => ?_⟩
    let φ : ((F P).toDescentData f).obj (Discrete.mk t) ⟶ ((F P).toDescentData f).obj M :=
      { hom i := homOfEq P ((ht i).trans (as_eq P (e.hom.hom i)).symm)
        comm := by intros; apply hom_eq }
    exact as_eq P (((F P).toDescentData f).preimage φ)
  · intro h
    have hfaith : ((F P).toDescentData f).Faithful := ⟨fun {_ _} _ _ _ => hom_eq P _ _⟩
    have hfull : ((F P).toDescentData f).Full := ⟨fun {M N} ψ => by
      have : M.as = N.as := by
        obtain ⟨t, -, ht⟩ := h (fun i => P.map (f i).op N.as)
          (Presieve.Arrows.toCompatible P f N.as).property
        exact (ht M.as fun i => as_eq P (ψ.hom i)).trans (ht N.as fun i => rfl).symm
      exact ⟨homOfEq P this, by ext i; apply hom_eq⟩⟩
    have hess : ((F P).toDescentData f).EssSurj := ⟨fun D => by
      have hx : Presieve.Arrows.Compatible P f (fun i => (D.obj i).as) := by
        intro i j Z gi gj hij
        exact as_eq P (D.hom (gi ≫ f i) gi gj rfl hij.symm)
      obtain ⟨t, ht, -⟩ := h _ hx
      exact ⟨Discrete.mk t, ⟨Pseudofunctor.DescentData.isoMk (fun i => isoOfEq P (ht i))
        (by intros; apply hom_eq)⟩⟩⟩
    exact ⟨hfaith, hfull, hess⟩

theorem isStackFor_iff {S : C} (R : Presieve S) :
    (F P).IsStackFor R ↔ Presieve.IsSheafFor P R := by
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.isStackFor_ofArrows_iff, key]

end TopStackAux

theorem solution {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) :
    (P ⋙ typeToCat.{w}).toPseudofunctor'.IsStack J ↔ Presieve.IsSheaf J P := by
  constructor
  · intro h S R hR
    exact (TopStackAux.isStackFor_iff R.arrows).1
      ((P ⋙ typeToCat.{w}).toPseudofunctor'.isStackFor' R hR)
  · intro h
    exact Pseudofunctor.IsStack.of_isStackFor
      (fun S R hR => (TopStackAux.isStackFor_iff R.arrows).2 (h R hR))
