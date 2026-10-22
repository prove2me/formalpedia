-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P14.objectClasses_group
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:31:09.4595+00:00
-- url     : https://prove2.me/submissions/59a500a0-3c3b-44f2-8b31-2a27d597c693

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

open QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

noncomputable def g73w_mul {C : Type u} [Category.{v} C] [MonoidalCategory C] :
    Mul (ObjectClasses C) :=
  ⟨Quotient.map₂ (fun x y : C => x ⊗ y)
    (fun _ _ hx _ _ hy => ⟨tensorIso (Classical.choice hx) (Classical.choice hy)⟩)⟩

theorem g73w_mul_mk {C : Type u} [Category.{v} C] [MonoidalCategory C] (x y : C) :
    (letI := (g73w_mul : Mul (ObjectClasses C)); objectClass x * objectClass y) =
      objectClass (x ⊗ y) := rfl

theorem solution {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (h : IsWeakTwoGroup C) :
    ∃ g : Group (ObjectClasses C),
      letI := g
      (∀ x y : C, objectClass x * objectClass y = objectClass (x ⊗ y)) ∧
      (1 : ObjectClasses C) = objectClass (𝟙_ C) ∧
      (∀ x y : C, IsWeakInverse x y → (objectClass x)⁻¹ = objectClass y) := by
  letI m : Mul (ObjectClasses C) := g73w_mul
  letI o : One (ObjectClasses C) := ⟨objectClass (𝟙_ C)⟩
  have hex : ∀ a : ObjectClasses C, ∃ b : ObjectClasses C, b * a = 1 := by
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      obtain ⟨y, _, ⟨e⟩⟩ := h.2 x
      exact ⟨objectClass y, Quotient.sound ⟨e⟩⟩
  letI iv : Inv (ObjectClasses C) := ⟨fun a => Classical.choose (hex a)⟩
  let G : Group (ObjectClasses C) := Group.ofLeftAxioms
    (by
      intro a b c
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      induction c using Quotient.inductionOn
      exact Quotient.sound ⟨α_ _ _ _⟩)
    (by
      intro a
      induction a using Quotient.inductionOn
      exact Quotient.sound ⟨λ_ _⟩)
    (fun a => Classical.choose_spec (hex a))
  refine ⟨G, fun x y => rfl, rfl, ?_⟩
  intro x y hxy
  apply inv_eq_of_mul_eq_one_right
  exact Quotient.sound hxy.1
