-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.crossWeightRegeneration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:15:53.134786+00:00
-- url     : https://prove2.me/submissions/c91d7e69-39dd-4eed-a979-8e27416bf9e5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59L
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59

abbrev mA : Mat := !![0,0,1; 0,0,0; 1,0,0]
abbrev mB : Mat := !![0,0,0; 0,0,1; 0,1,0]
abbrev mP : Mat := !![1,0,0; 0,-1,0; 0,0,0]
abbrev mR : Mat := !![0,1,0; 1,0,0; 0,0,0]
abbrev mD : Mat := !![1,0,0; 0,1,0; 0,0,-2]
abbrev Jx : Mat := rotationGenerator ![1,0,0]
abbrev Jy : Mat := rotationGenerator ![0,1,0]
abbrev Jz : Mat := rotationGenerator ![0,0,1]

lemma memX {X : Mat} (h : X ∈ weightOneSymmetric) : ∃ x1 x2 : ℝ, X = x1 • mA + x2 • mB := by
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.mp h
  exact ⟨a, b, h.symm⟩

lemma memZ {Z : Mat} (h : Z ∈ weightTwoDeviator) :
    ∃ z1 z2 z3 : ℝ, Z = z1 • mP + z2 • mR + z3 • mD := by
  unfold weightTwoDeviator at h
  obtain ⟨a, y, hy, rfl⟩ := Submodule.mem_span_insert.mp h
  obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.mp hy
  exact ⟨a, b, c, by abel⟩

lemma brk (x1 x2 z1 z2 z3 : ℝ) :
    (x1 • mA + x2 • mB) * (z1 • mP + z2 • mR + z3 • mD) -
      (z1 • mP + z2 • mR + z3 • mD) * (x1 • mA + x2 • mB) =
    (x1*z2 - x2*z1 + 3*x2*z3) • Jx + (-x1*z1 - 3*x1*z3 - x2*z2) • Jy := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotationGenerator] <;> ring

lemma brkJ (c d : ℝ) : Jz * (c • Jx + d • Jy) - (c • Jx + d • Jy) * Jz = (-d) • Jx + c • Jy := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotationGenerator] <;> ring

lemma Jxy_ne (c d : ℝ) (h : c • Jx + d • Jy = 0) : c = 0 ∧ d = 0 := by
  have h1 := congrFun (congrFun h 2) 1
  have h2 := congrFun (congrFun h 0) 2
  simp [rotationGenerator] at h1 h2
  exact ⟨h1, h2⟩

lemma span_eq (c d : ℝ) (h : c ≠ 0 ∨ d ≠ 0) :
    Submodule.span ℝ {c • Jx + d • Jy, (-d) • Jx + c • Jy} = weightOneRotation := by
  have hn : c ^ 2 + d ^ 2 ≠ 0 := by
    rcases h with h | h <;> positivity
  unfold weightOneRotation
  apply le_antisymm
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Submodule.mem_span_pair.mpr ⟨c, d, rfl⟩, Submodule.mem_span_pair.mpr ⟨-d, c, rfl⟩⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · refine Submodule.mem_span_pair.mpr ⟨c / (c^2+d^2), -d / (c^2+d^2), ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator] <;> field_simp <;> ring
    · refine Submodule.mem_span_pair.mpr ⟨d / (c^2+d^2), c / (c^2+d^2), ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [rotationGenerator] <;> field_simp <;> ring

end X4P59L

open QAlgorithms.Papers.Independent.Information100.P59 X4P59L in
theorem solution :
    (∀ X ∈ weightOneSymmetric, ∀ Z ∈ weightTwoDeviator,
      X * Z - Z * X ∈ weightOneRotation) ∧
    (∀ Z ∈ weightTwoDeviator, Z ≠ 0 →
      ∃ X ∈ weightOneSymmetric, X * Z - Z * X ≠ 0 ∧
        Submodule.span ℝ {X * Z - Z * X,
          rotationGenerator ![0,0,1] * (X * Z - Z * X) -
            (X * Z - Z * X) * rotationGenerator ![0,0,1]} = weightOneRotation) := by
  constructor
  · intro X hX Z hZ
    obtain ⟨x1, x2, rfl⟩ := memX hX
    obtain ⟨z1, z2, z3, rfl⟩ := memZ hZ
    rw [brk]
    exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
  · intro Z hZ hZ0
    obtain ⟨z1, z2, z3, rfl⟩ := memZ hZ
    have key : ∀ x1 x2 : ℝ, (x1*z2 - x2*z1 + 3*x2*z3 ≠ 0 ∨ -x1*z1 - 3*x1*z3 - x2*z2 ≠ 0) →
        ∃ X ∈ weightOneSymmetric, X * (z1 • mP + z2 • mR + z3 • mD) - (z1 • mP + z2 • mR + z3 • mD) * X ≠ 0 ∧
        Submodule.span ℝ {X * (z1 • mP + z2 • mR + z3 • mD) - (z1 • mP + z2 • mR + z3 • mD) * X,
          rotationGenerator ![0,0,1] * (X * (z1 • mP + z2 • mR + z3 • mD) - (z1 • mP + z2 • mR + z3 • mD) * X) -
            (X * (z1 • mP + z2 • mR + z3 • mD) - (z1 • mP + z2 • mR + z3 • mD) * X) *
              rotationGenerator ![0,0,1]} = weightOneRotation := by
      intro x1 x2 hne
      refine ⟨x1 • mA + x2 • mB, Submodule.mem_span_pair.mpr ⟨x1, x2, rfl⟩, ?_, ?_⟩
      · rw [brk]
        intro h0
        have := Jxy_ne _ _ h0
        rcases hne with h | h
        · exact h this.1
        · exact h this.2
      · rw [brk, brkJ]
        exact span_eq _ _ hne
    by_cases h1 : z2 ≠ 0 ∨ -z1 - 3*z3 ≠ 0
    · apply key 1 0; simpa using h1
    · push Not at h1
      apply key 0 1
      by_contra h2
      push Not at h2
      apply hZ0
      have : z1 = 0 ∧ z2 = 0 ∧ z3 = 0 := by
        refine ⟨by linarith, h1.1, by linarith⟩
      obtain ⟨rfl, rfl, rfl⟩ := this
      simp
