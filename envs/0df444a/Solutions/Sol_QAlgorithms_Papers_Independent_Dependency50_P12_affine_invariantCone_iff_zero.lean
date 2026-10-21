-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.affine_invariantCone_iff_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:25:31.562264+00:00
-- url     : https://prove2.me/submissions/f3bfe7bd-e797-40a1-bd51-450f9531dc8f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup


theorem g55a_lim {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [ContinuousAdd X] [ContinuousSMul ℝ X]
    {W : Set X} (hcl : IsClosed W) (hc : IsCone W) {w u : X}
    (h : ∀ s : ℝ, w + s • u ∈ W) : u ∈ W := by
  have ht : Filter.Tendsto (fun l : ℝ => l⁻¹ • w + u) Filter.atTop (nhds u) := by
    have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w).add_const u
    simpa using this
  refine hcl.mem_of_tendsto ht ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with l hl
  have := hc.2.2 l⁻¹ (inv_nonneg.2 hl.le) _ (h l)
  rwa [smul_add, smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at this

theorem g55a_expAd_nil {n : ℕ} (T w : affineAlgebra n) (h : ⁅T, ⁅T, w⁆⁆ = 0) :
    expAd T w = w + ⁅T, w⁆ := by
  unfold expAd
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, adMap]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have h2 : (adMap T ^ 2) w = 0 := by
      simp [pow_two, adMap, h]
    have hz : ∀ m : ℕ, (adMap T ^ (m + 2)) w = 0 := by
      intro m
      rw [pow_add, Module.End.mul_apply, h2, map_zero]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [hz, smul_zero]

theorem g55a_aff_pos (m : ℕ) :
    ¬ (∃ W : Set (affineAlgebra (m+1)), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra (m+1), ∃ Y ∈ W, ∃ Z ∈ W, X = Y - Z) ∧
      (∀ X : affineAlgebra (m+1), expAd X '' W ⊆ W)) := by
  rintro ⟨W, hcl, hc, hedge, hgen, hinv⟩
  have : ContinuousSMul ℝ (affineAlgebra (m+1)) :=
    inferInstanceAs (ContinuousSMul ℝ (affineAlgebra (m+1)).toSubmodule)
  have hl : (Fin.last (m+1)) ≠ 0 := by simp [Fin.ext_iff]
  let X0 : affineAlgebra (m+1) := ⟨Matrix.single 0 0 1, by
    intro j; simp [Matrix.single_apply, hl]⟩
  let T : affineAlgebra (m+1) := ⟨Matrix.single 0 (Fin.last (m+1)) 1, by
    intro j; simp [Matrix.single_apply, hl]⟩
  -- find w ∈ W with w 0 0 ≠ 0
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 ≠ 0 := by
    obtain ⟨Y, hY, Z, hZ, hXYZ⟩ := hgen X0
    have h := congrArg (fun M : affineAlgebra (m+1) => (M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0) hXYZ
    change (Matrix.single (0 : Fin (m+2)) (0 : Fin (m+2)) (1:ℝ)) 0 0 =
      (Y : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 - (Z : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 at h
    by_cases hY0 : (Y : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 = 0
    · refine ⟨Z, hZ, ?_⟩
      intro hZ0; rw [hY0, hZ0] at h; simp at h
    · exact ⟨Y, hY, hY0⟩
  have hwl : ∀ j, (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (Fin.last (m+1)) j = 0 := w.2
  have h1 : (T : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) * w = 0 := by
    ext i j; simp [T, Matrix.mul_apply, Matrix.single_apply, hwl, ite_and]
  have h2 : (T : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) * T = 0 := by
    ext i j; simp [T, Matrix.mul_apply, Matrix.single_apply, hl.symm, ite_and]
  have hT0 : ⁅T, ⁅T, w⁆⁆ = 0 := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def]
    simp only [mul_sub, sub_mul, ← Matrix.mul_assoc, h1, h2, Matrix.zero_mul, Matrix.mul_zero]
    rw [Matrix.mul_assoc (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ), h2]
    simp
  have hTT : ∀ s : ℝ, ⁅s • T, ⁅s • T, w⁆⁆ = 0 := by
    intro s
    simp [smul_lie, lie_smul, hT0]
  set u := ⁅T, w⁆ with hu
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg (fun M : affineAlgebra (m+1) =>
      (M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 (Fin.last (m+1))) h
    simp only [hu, LieSubalgebra.coe_bracket, Ring.lie_def, h1, Matrix.sub_apply] at this
    simp [T, Matrix.mul_apply, Matrix.single_apply] at this
    exact hw0 this
  have hline : ∀ s : ℝ, w + s • u ∈ W := by
    intro s
    have hm := hinv (s • T) ⟨w, hw, rfl⟩
    rw [g55a_expAd_nil _ _ (hTT s), smul_lie] at hm
    exact hm
  have hu1 : u ∈ W := g55a_lim hcl hc hline
  have hu2 : -u ∈ W := g55a_lim hcl hc (fun s => by simpa using hline (-s))
  have : u ∈ edge W := ⟨hu1, hu2⟩
  rw [hedge] at this
  exact hu0 this

theorem g55a_aff_zero_sub (X : affineAlgebra 0) : X = 0 := by
  apply Subtype.ext
  ext i j
  have hi : i = Fin.last 0 := by
    apply Fin.ext
    have hbound : i.val < 1 := i.isLt
    omega
  subst hi
  exact X.2 j

/-- arXiv:2608.27330v1, PDF p.37, Proposition 6.1.
Coordinates cover every finite-dimensional real V. Generating means W-W=aff(V),
and the zero-dimensional boundary is retained in the equivalence. -/
theorem solution (n : ℕ) :
    (∃ W : Set (affineAlgebra n), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra n, ∃ Y ∈ W, ∃ Z ∈ W, X = Y - Z) ∧
      (∀ X : affineAlgebra n, expAd X '' W ⊆ W)) ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact g55a_aff_pos m h
  · rintro rfl
    refine ⟨{0}, isClosed_singleton, ⟨rfl, convex_singleton 0, ?_⟩, ?_, ?_, ?_⟩
    · intro a _ x _; exact g55a_aff_zero_sub _
    · ext x; simp [edge, g55a_aff_zero_sub x]
    · intro X; exact ⟨0, rfl, 0, rfl, by rw [sub_zero]; exact g55a_aff_zero_sub X⟩
    · intro X y _; exact g55a_aff_zero_sub y


end

