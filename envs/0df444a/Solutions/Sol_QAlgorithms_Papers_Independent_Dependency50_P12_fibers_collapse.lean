-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.fibers_collapse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:04:17.350976+00:00
-- url     : https://prove2.me/submissions/6900ed23-87e8-46db-8f82-1536837ee040

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


theorem g55a_cs_add (D : LeviSplitting A) (S T : D.s) : ((S + T : D.s) : A) = (S : A) + (T : A) := rfl
theorem g55a_cs_smul (D : LeviSplitting A) (a : ℝ) (S : D.s) : ((a • S : D.s) : A) = a • (S : A) := rfl

theorem g55a_smul_mem {W : Set A} (hW : IsCone W) {a : ℝ} (ha : 0 ≤ a) {x : A} (hx : x ∈ W) :
    a • x ∈ W := hW.2.2 a ha x hx

theorem g55a_fiberProps (D : LeviSplitting A) (W : Set A) (hW : IsLieWedge W) :
    FiberProperties D W := by
  obtain ⟨hcl, hcone⟩ := hW.1, hW.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S ⟨x, hx, rfl⟩
    refine ⟨⟨piR D x, ?_⟩, ?_, ?_⟩
    · show ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ W
      rw [g55a_decomp]; exact hx
    · exact hcl.preimage (continuous_const.add continuous_subtype_val)
    · intro R1 h1 R2 h2 a b ha hb hab
      show ((piS D x : D.s) : A) + ((a • R1 + b • R2 : D.r) : A) ∈ W
      have := hcone.2.1 h1 h2 ha hb hab
      convert this using 1
      simp only [LieSubmodule.coe_add, LieSubmodule.coe_smul]
      obtain rfl : b = 1 - a := by linarith
      module
  · ext R; simp [fiber, radicalSlice]
  · intro S _ T _ R hR Q hQ
    show ((S + T : D.s) : A) + ((R + Q : D.r) : A) ∈ W
    have := g55a_add hcone hR hQ
    convert this using 1
    simp only [g55a_cs_add, LieSubmodule.coe_add]; abel
  · rintro a ha S _ _ ⟨R, hR, rfl⟩
    show ((a • S : D.s) : A) + ((a • R : D.r) : A) ∈ W
    have := g55a_smul_mem hcone ha hR
    convert this using 1
    simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add]
  · intro a ha S _
    apply Set.Subset.antisymm
    · rintro _ ⟨R, hR, rfl⟩
      show ((a • S : D.s) : A) + ((a • R : D.r) : A) ∈ W
      have := g55a_smul_mem hcone ha.le hR
      convert this using 1
      simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add]
    · intro R hR
      refine ⟨a⁻¹ • R, ?_, ?_⟩
      · show ((S : D.s) : A) + ((a⁻¹ • R : D.r) : A) ∈ W
        have := g55a_smul_mem hcone (inv_nonneg.2 ha.le) hR
        convert this using 1
        simp only [g55a_cs_smul, LieSubmodule.coe_smul, smul_add, smul_smul,
          inv_mul_cancel₀ ha.ne', one_smul]
      · simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · have : fiberGraph D (quotientCone D W) (fiber D W) =
        (fun p : D.s × D.r => ((p.1 : D.s) : A) + ((p.2 : D.r) : A)) ⁻¹' W := by
      ext p
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        exact ⟨⟨_, h, g55a_piS D p.1 p.2⟩, h⟩
    rw [this]
    exact hcl.preimage ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd))

theorem g55a_collapse (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W)
    (hC : ∀ S ∈ quotientCone D W, (S : A) ∈ edge W) :
    (∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) ∧
    W = {x | ∃ S ∈ quotientCone D W, ∃ R ∈ radicalSlice D W,
      x = (S : A) + (R : A)} ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ →
      Module.finrank ℝ D.s < Module.finrank ℝ A ∧
      Module.finrank ℝ D.r < Module.finrank ℝ A) := by
  have hcone := hW.2.1
  have hfib : ∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W := by
    intro S hS
    obtain ⟨h1, h2⟩ := hC S hS
    ext R
    constructor
    · intro hR
      show (R : A) ∈ W
      have := g55a_add hcone h2 hR
      simpa using this
    · intro hR
      exact g55a_add hcone h1 hR
  refine ⟨hfib, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hS : piS D x ∈ quotientCone D W := ⟨x, hx, rfl⟩
      refine ⟨_, hS, piR D x, ?_, (g55a_decomp D x).symm⟩
      rw [← hfib _ hS]
      show ((piS D x : D.s) : A) + ((piR D x : D.r) : A) ∈ W
      rw [g55a_decomp]; exact hx
    · rintro ⟨S, hS, R, hR, rfl⟩
      exact g55a_add hcone (hC S hS).1 hR
  · intro hs hr
    have hsum := Submodule.finrank_add_eq_of_isCompl D.complementary
    have h1 : 0 < Module.finrank ℝ D.s.toSubmodule := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      by_contra hc
      push Not at hc
      apply hs
      ext x
      constructor
      · intro hx
        have := hc ⟨x, hx⟩
        simpa using congrArg Subtype.val this
      · intro hx
        rw [LieSubalgebra.mem_bot] at hx
        rw [hx]; exact D.s.zero_mem
    have h2 : 0 < Module.finrank ℝ D.r.toSubmodule := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      by_contra hc
      push Not at hc
      apply hr
      ext x
      constructor
      · intro hx
        have := hc ⟨x, hx⟩
        simpa using congrArg Subtype.val this
      · intro hx
        rw [LieSubmodule.mem_bot] at hx
        rw [hx]; exact D.r.zero_mem
    exact ⟨by change Module.finrank ℝ D.s.toSubmodule < _; omega,
      by change Module.finrank ℝ D.r.toSubmodule < _; omega⟩

end AbstractResults


open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- arXiv:2608.27330v1, PDF p.27, Proposition 4.12.
The two strict dimension reductions are conditional on BOTH factors being nonzero. -/
theorem solution (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W)
    (hC : ∀ S ∈ quotientCone D W, (S : A) ∈ edge W) :
    (∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) ∧
    W = {x | ∃ S ∈ quotientCone D W, ∃ R ∈ radicalSlice D W,
      x = (S : A) + (R : A)} ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ →
      Module.finrank ℝ D.s < Module.finrank ℝ A ∧
      Module.finrank ℝ D.r < Module.finrank ℝ A) := by
  exact g55a_collapse D W hW hC

end AbstractResults


end

