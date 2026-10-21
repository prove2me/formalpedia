-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.edge_fiber_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:01:21.748593+00:00
-- url     : https://prove2.me/submissions/4306165f-5d57-470f-83f9-58b749e677cc

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

set_option linter.unusedSectionVars false
section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

theorem g55a_decomp (D : LeviSplitting A) (x : A) :
    ((piS D x : D.s) : A) + ((piR D x : D.r) : A) = x := by
  have := (coords D).apply_symm_apply x
  exact this

theorem g55a_piS (D : LeviSplitting A) (S : D.s) (R : D.r) :
    piS D ((S : A) + (R : A)) = S := by
  have : (coords D).symm (coords D (S, R)) = (S, R) := (coords D).symm_apply_apply _
  exact congrArg Prod.fst this

theorem g55a_piR (D : LeviSplitting A) (S : D.s) (R : D.r) :
    piR D ((S : A) + (R : A)) = R := by
  have : (coords D).symm (coords D (S, R)) = (S, R) := (coords D).symm_apply_apply _
  exact congrArg Prod.snd this

theorem g55a_add {W : Set A} (hW : IsCone W) {x y : A} (hx : x ∈ W) (hy : y ∈ W) :
    x + y ∈ W := by
  have h := hW.2.1 hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have h2 := hW.2.2 2 (by norm_num) _ h
  convert h2 using 1
  rw [smul_add, smul_smul, smul_smul]; norm_num

theorem g55a_edge_iff (D : LeviSplitting A) (W : Set A) (S : D.s) (R : D.r) :
    (S : A) + (R : A) ∈ edge W ↔
      S ∈ edge (quotientCone D W) ∧ R ∈ fiber D W S ∧ -R ∈ fiber D W (-S) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : ((-S : D.s) : A) + ((-R : D.r) : A) ∈ W := by
      simpa [neg_add, add_comm] using h2
    refine ⟨⟨⟨_, h1, g55a_piS D S R⟩, ⟨_, h2', ?_⟩⟩, h1, h2'⟩
    rw [g55a_piS]
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, ?_⟩
    have : ((-S : D.s) : A) + ((-R : D.r) : A) ∈ W := h2
    simpa [neg_add, add_comm] using this

theorem g55a_edge_eq (D : LeviSplitting A) (W : Set A) :
    edge W = candidateEdge D (quotientCone D W) (fiber D W) := by
  ext x
  constructor
  · intro hx
    rw [← g55a_decomp D x] at hx
    obtain ⟨h1, h2, h3⟩ := (g55a_edge_iff D W _ _).1 hx
    exact ⟨_, h1, _, h2, h3, (g55a_decomp D x).symm⟩
  · rintro ⟨S, hS, R, h1, h2, rfl⟩
    exact (g55a_edge_iff D W S R).2 ⟨hS, h1, h2⟩

end AbstractResults


open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- arXiv:2608.27330v1, PDF p.26, Corollary 4.11, including Equation (42). -/
theorem solution (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    (∀ (S : D.s) (R : D.r), (S : A) + (R : A) ∈ edge W ↔
      S ∈ edge (quotientCone D W) ∧ R ∈ fiber D W S ∧ -R ∈ fiber D W (-S)) ∧
    edge W = candidateEdge D (quotientCone D W) (fiber D W) := by
  exact ⟨fun S R => g55a_edge_iff D W S R, g55a_edge_eq D W⟩

end AbstractResults


end

