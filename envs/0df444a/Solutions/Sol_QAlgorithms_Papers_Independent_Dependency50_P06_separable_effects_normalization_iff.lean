-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.separable_effects_normalization_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:50:39.416685+00:00
-- url     : https://prove2.me/submissions/bf8b9283-7628-484d-a6e1-0640499170b2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

section OperationalDefinitions

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℝ C]

variable [MonoidalCategory C] [SymmetricCategory C]

variable [MonoidalPreadditive C] [MonoidalLinear ℝ C]

lemma g52a_det_seq (T : OperationalTheory C) {X Y Z : C} {x : X ⟶ Y} {y : Y ⟶ Z}
    (hx : IsDeterministic T x) (hy : IsDeterministic T y) : IsDeterministic T (x ≫ y) := by
  have := T.sequential_tests [x] [y] hx hy
  simpa [IsDeterministic] using this

lemma g52a_det_par (T : OperationalTheory C) {X Y Z W : C} {x : X ⟶ Y} {y : Z ⟶ W}
    (hx : IsDeterministic T x) (hy : IsDeterministic T y) : IsDeterministic T (x ⊗ₘ y) := by
  have := T.parallel_tests [x] [y] hx hy
  simpa [IsDeterministic] using this

lemma g52a_complete_single (T : OperationalTheory C) {A B : C} (f : A ⟶ B)
    (h : CompleteUpperBound T f) : SingleUpperBound T f := by
  intro rho hrho d hd
  have := h (𝟙_ C) (rho ≫ (ρ_ A).inv) (g52a_det_seq T hrho (T.right_unitor_inverse_test A))
    ((ρ_ B).hom ≫ d) (g52a_det_seq T (T.right_unitor_test B) hd)
  have e : (rho ≫ (ρ_ A).inv) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ B).hom ≫ d = rho ≫ f ≫ d := by
    simp only [tensorHom_id, Category.assoc, rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]
  rwa [e] at this

lemma g52a_tail {A B S : C} (f : A ⟶ B) (a : B ⟶ 𝟙_ C) (b : S ⟶ 𝟙_ C) :
    (f ⊗ₘ 𝟙 S) ≫ (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = (A ◁ b) ≫ (ρ_ A).hom ≫ f ≫ a := by
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, tensorHom_def', Category.assoc,
    unitors_equal, rightUnitor_naturality]

lemma g52a_head {A B S : C} (f : A ⟶ B) (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ S) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (f ⊗ₘ 𝟙 S) = a ≫ f ≫ (ρ_ B).inv ≫ (B ◁ b) := by
  rw [tensorHom_comp_tensorHom, Category.comp_id, MonoidalCategory.tensorHom_def, unitors_inv_equal,
    ← Category.assoc ((ρ_ (𝟙_ C)).inv), ← rightUnitor_inv_naturality]
  simp only [Category.assoc]

lemma g52a_rho_det (T : OperationalTheory C) {A S : C} {rho : 𝟙_ C ⟶ A ⊗ S} {b : S ⟶ 𝟙_ C}
    (hrho : IsDeterministic T rho) (hb : IsDeterministic T b) :
    IsDeterministic T (rho ≫ (A ◁ b) ≫ (ρ_ A).hom) := by
  refine g52a_det_seq T hrho (g52a_det_seq T ?_ (T.right_unitor_test A))
  have := g52a_det_par T (T.identity_test A) hb
  rwa [id_tensorHom] at this

lemma g52a_d_det (T : OperationalTheory C) {B S : C} {d : B ⊗ S ⟶ 𝟙_ C} {b : 𝟙_ C ⟶ S}
    (hd : IsDeterministic T d) (hb : IsDeterministic T b) :
    IsDeterministic T ((ρ_ B).inv ≫ (B ◁ b) ≫ d) := by
  refine g52a_det_seq T (T.right_unitor_inverse_test B) (g52a_det_seq T ?_ hd)
  have := g52a_det_par T (T.identity_test B) hb
  rwa [id_tensorHom] at this

lemma g52a_head_assoc {A B S : C} {Z : C} (f : A ⟶ B) (a : 𝟙_ C ⟶ A) (b : 𝟙_ C ⟶ S)
    (h : B ⊗ S ⟶ Z) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (f ⊗ₘ 𝟙 S) ≫ h = a ≫ f ≫ (ρ_ B).inv ≫ (B ◁ b) ≫ h := by
  rw [← Category.assoc (a ⊗ₘ b), ← Category.assoc (λ_ (𝟙_ C)).inv, g52a_head]
  simp only [Category.assoc]

/-- PDF p.26: dual separable deterministic-effect reduction; every deterministic
output effect remains quantified in both inequalities. -/
theorem solution (T : OperationalTheory C)
    (hT : HasSeparableDeterministicEffects T) {A B : C} (f : A ⟶ B) :
    CompleteUpperBound T f ↔ SingleUpperBound T f := by
  refine ⟨g52a_complete_single T f, fun h S rho hrho d hd => ?_⟩
  obtain ⟨n, w, a, b, hw, hsum, hr⟩ := hT B S d hd
  rw [hr, Preadditive.comp_sum, Preadditive.comp_sum, map_sum]
  have hterm : ∀ i, T.scalar (rho ≫ (f ⊗ₘ 𝟙 S) ≫ (w i • ((a i ⊗ₘ b i) ≫ (λ_ (𝟙_ C)).hom))) ≤
      w i * 1 := by
    intro i
    rw [Linear.comp_smul, Linear.comp_smul, map_smul, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (hw i).1
    rw [g52a_tail]
    have := h _ (g52a_rho_det T hrho (hw i).2.2) (a i) (hw i).2.1
    simpa only [Category.assoc] using this
  calc ∑ i, T.scalar (rho ≫ (f ⊗ₘ 𝟙 S) ≫ (w i • ((a i ⊗ₘ b i) ≫ (λ_ (𝟙_ C)).hom)))
      ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ => hterm i
    _ = 1 := by simp [hsum]

end OperationalDefinitions


end

