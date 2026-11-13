-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.internalCategoriesInSet
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:29:58.147425+00:00
-- url     : https://prove2.me/submissions/47b64cc4-3c92-475a-9855-0a49ddd15f80

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF pp. 6–8: internal categories in Set and ordinary small categories have
mutually inverse structure translations. Objects stay fixed; arrows are identified
by the displayed canonical equivalences. Every reconstruction equation for
composition is restricted to the source's composable pairs. -/
theorem solution :
    (∀ {A : Type u} {O : Type v} (D : CategoryMaps A O) (h : CategoryDiagrams D),
      letI := categoryOfMaps D h
      let E := mapsOfCategory O
      let q := totalArrowEquiv D h
      (∀ a, E.source (q a) = D.source a ∧ E.target (q a) = D.target a) ∧
      (∀ x, E.identity x = q (D.identity x)) ∧
      (∀ f g, D.target f = D.source g →
        E.compose (q g) (q f) = q (D.compose g f))) ∧
    (∀ (O : Type v) [Category.{u} O], CategoryDiagrams (mapsOfCategory O) ∧
      (∀ x, (mapsOfCategory O).identity x = ⟨x, x, 𝟙 x⟩) ∧
      (∀ x y z (f : x ⟶ y) (g : y ⟶ z),
        (mapsOfCategory O).compose ⟨y, z, g⟩ ⟨x, y, f⟩ = ⟨x, z, f ≫ g⟩) ∧
      (∀ x y (f : x ⟶ y), (totalHomEquiv O x y f).val = ⟨x, y, f⟩)) := by
  classical
  constructor
  · intro A O D h
    letI := categoryOfMaps D h
    dsimp only
    have hcast {x y : O} (hxy : x = y) :
        (eqToHom hxy : x ⟶ y).val = D.identity x := by cases hxy; rfl
    refine ⟨fun a => ⟨rfl,rfl⟩,?_,?_⟩
    · intro x
      apply (totalArrowEquiv D h).symm.injective
      rfl
    · intro f g hfg
      have hc {x y z w : O} (f : x ⟶ y) (g : z ⟶ w) (he : y = z) :
          (mapsOfCategory O).compose ⟨z,w,g⟩ ⟨x,y,f⟩ = ⟨x,w,f ≫ eqToHom he ≫ g⟩ := by
        cases he
        simp [mapsOfCategory] <;> rfl
      apply (totalArrowEquiv D h).symm.injective
      change (totalArrowEquiv D h).symm
        ((mapsOfCategory O).compose ⟨D.source g,D.target g,⟨g,rfl,rfl⟩⟩
          ⟨D.source f,D.target f,⟨f,rfl,rfl⟩⟩) = D.compose g f
      erw [hc _ _ hfg]
      change D.compose (D.compose g (eqToHom hfg : D.target f ⟶ D.source g).val) f = D.compose g f
      erw [hcast,hfg,h.compose_identity]
  · intro O inst
    refine ⟨?_,fun _ => rfl,?_,fun _ _ _ => rfl⟩
    · constructor
      · intro x; rfl
      · intro x; rfl
      · rintro ⟨x,y,f⟩ ⟨y',z,g⟩ h
        change y = y' at h
        subst y'
        simp [mapsOfCategory] <;> rfl
      · rintro ⟨x,y,f⟩ ⟨y',z,g⟩ h
        change y = y' at h
        subst y'
        simp [mapsOfCategory] <;> rfl
      · rintro ⟨x,y,f⟩
        simp [mapsOfCategory] <;> rfl
      · rintro ⟨x,y,f⟩
        simp [mapsOfCategory] <;> rfl
      · rintro ⟨x,y,f⟩ ⟨y',z,g⟩ ⟨z',w,k⟩ hfg hgk
        change y = y' at hfg
        change z = z' at hgk
        subst y'; subst z'
        simp [mapsOfCategory,Category.assoc] <;> rfl
    · intro x y z f g
      simp [mapsOfCategory] <;> rfl
