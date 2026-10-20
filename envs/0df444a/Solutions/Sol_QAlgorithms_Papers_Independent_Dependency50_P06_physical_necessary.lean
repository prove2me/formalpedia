-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.physical_necessary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:49:42.323985+00:00
-- url     : https://prove2.me/submissions/85daf34a-f156-4cda-9f9a-f82670a8fcfb

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

/-- PDF pp.22–23, Theorem F.10: physicality implies cone preservation on
ancillary physical states and the deterministic-state/effect upper bound.
Necessity only in an arbitrary OPT, not an unrestricted-theory iff. -/
theorem solution (T : OperationalTheory C) {A B : C} (f : A ⟶ B)
    (hf : IsPhysical T f) :
    (∀ S : C, ∀ rho : (𝟙_ C) ⟶ (A ⊗ S), IsPhysical T rho →
      InStateCone T (B ⊗ S) (rho ≫ (f ⊗ₘ 𝟙 S))) ∧ CompleteUpperBound T f := by
  obtain ⟨t, ht, hft⟩ := hf
  have hpar : ∀ S : C, (t.flatMap fun f' => [𝟙 S].map fun g => f' ⊗ₘ g) ∈ T.tests (A ⊗ S) (B ⊗ S) ∧
      (f ⊗ₘ 𝟙 S) ∈ (t.flatMap fun f' => [𝟙 S].map fun g => f' ⊗ₘ g) := by
    intro S
    refine ⟨T.parallel_tests t [𝟙 S] ht (T.identity_test S), ?_⟩
    exact List.mem_flatMap.mpr ⟨f, hft, by simp⟩
  have hseq : ∀ S : C, ∀ (t0 : List ((𝟙_ C) ⟶ (A ⊗ S))) (rho : (𝟙_ C) ⟶ (A ⊗ S)),
      t0 ∈ T.tests (𝟙_ C) (A ⊗ S) → rho ∈ t0 →
      ∃ t2 ∈ T.tests (𝟙_ C) (B ⊗ S), rho ≫ (f ⊗ₘ 𝟙 S) ∈ t2 := by
    intro S t0 rho h0 hr
    obtain ⟨h1, h2⟩ := hpar S
    exact ⟨_, T.sequential_tests t0 _ h0 h1, List.mem_flatMap.mpr ⟨rho, hr, List.mem_map.mpr
      ⟨_, h2, rfl⟩⟩⟩
  refine ⟨fun S rho ⟨t0, h0, hr⟩ => ?_, fun S rho hrho d hd => ?_⟩
  · obtain ⟨t2, h2, hm⟩ := hseq S t0 rho h0 hr
    refine ⟨1, fun _ => 1, fun _ => rho ≫ (f ⊗ₘ 𝟙 S), fun _ => ⟨zero_le_one, t2, h2, hm⟩, ?_⟩
    simp
  · obtain ⟨t2, h2, hm⟩ := hseq S [rho] rho hrho (List.mem_singleton_self _)
    have h3 := T.sequential_tests t2 [d] h2 hd
    have hm3 : (rho ≫ (f ⊗ₘ 𝟙 S)) ≫ d ∈ t2.flatMap fun x => [d].map fun g => x ≫ g :=
      List.mem_flatMap.mpr ⟨_, hm, by simp⟩
    obtain ⟨hnn, hsum⟩ := T.closed_test _ h3
    have hle := List.single_le_sum (l := (t2.flatMap fun x => [d].map fun g => x ≫ g).map
      fun g => T.scalar g) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hnn y hy) (T.scalar ((rho ≫ (f ⊗ₘ 𝟙 S)) ≫ d))
      (List.mem_map.mpr ⟨_, hm3, rfl⟩)
    rw [hsum, Category.assoc] at hle
    exact hle

end OperationalDefinitions


end

