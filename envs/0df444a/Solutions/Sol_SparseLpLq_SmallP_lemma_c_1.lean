-- Prove2me | solution 1 for SparseLpLq.SmallP.lemma_c_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:49:25.628923+00:00
-- url     : https://prove2.me/submissions/ffa6c5b9-6110-488b-b378-3104aa2f3e1e

import Definitions.Def_SparseLpLq_SmallP_Setting
import Init
import Mathlib


section
namespace Queelius.SparseHalfspaces
open Matrix
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem signed_dot_le (u v : ι → ℝ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    u ⬝ᵥ v ≤ ∑ i, |v i| := by
  apply Finset.sum_le_sum
  intro i hi
  rcases hu i with h | h
  · simpa [h] using le_abs_self (v i)
  · simpa [h] using neg_le_abs (v i)

noncomputable def maximizingSign (v : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ v i then 1 else -1

theorem maximizingSign_values (v : ι → ℝ) (i : ι) :
    maximizingSign v i = 1 ∨ maximizingSign v i = -1 := by
  unfold maximizingSign
  split_ifs <;> simp

theorem maximizingSign_dot (v : ι → ℝ) : maximizingSign v ⬝ᵥ v = ∑ i, |v i| := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 ≤ v i
  · simp [maximizingSign, h, abs_of_nonneg h]
  · simp [maximizingSign, h, abs_of_neg (lt_of_not_ge h)]

theorem sum_abs_le_iff (v : ι → ℝ) (σ : ℝ) :
    (∑ i, |v i|) ≤ σ ↔ ∀ u : ι → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ v ≤ σ := by
  constructor
  · intro h u hu
    exact (signed_dot_le u v hu).trans h
  · intro h
    simpa only [maximizingSign_dot] using h (maximizingSign v) (maximizingSign_values v)

theorem qNorm_one {m : ℕ} (v : Fin m → ℝ) : SparseLpLq.SmallP.qNorm 1 v = ∑ i, |v i| := by
  simp [SparseLpLq.SmallP.qNorm, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

theorem feasible_halfspaces {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (σ : ℝ) :
    SparseLpLq.SmallP.FEA A b σ 1 =
      {x | ∀ u : Fin m → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b + σ} := by
  ext x
  change SparseLpLq.SmallP.qNorm 1 (A *ᵥ x - b) ≤ σ ↔ _
  rw [qNorm_one, sum_abs_le_iff]
  constructor
  · intro h u hu
    have hh := h u hu
    rw [dotProduct_sub] at hh
    linarith
  · intro h u hu
    rw [dotProduct_sub]
    have hh := h u hu
    linarith
end Queelius.SparseHalfspaces

open scoped ENNReal Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) :
    SparseLpLq.SmallP.FEA A b σ 1 =
      {x | ∀ u : Fin m → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b + σ} :=
  Queelius.SparseHalfspaces.feasible_halfspaces A b σ

end

section
namespace Queelius.SparseHalfspaces.Controls
open Matrix
open scoped ENNReal

theorem zero_radius {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    x ∈ SparseLpLq.SmallP.FEA A b 0 1 ↔ A *ᵥ x = b := by
  change ‖(WithLp.toLp 1 (A *ᵥ x - b) : PiLp 1 (fun _ : Fin m => ℝ))‖ ≤ 0 ↔ _
  rw [norm_le_zero_iff]
  simpa only [← WithLp.toLp_sub, WithLp.toLp_eq_zero] using (sub_eq_zero : A *ᵥ x - b = 0 ↔ A *ᵥ x = b)

theorem negative_radius {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (σ : ℝ) (hσ : σ < 0) :
    SparseLpLq.SmallP.FEA A b σ 1 = ∅ := by
  ext x
  simp only [SparseLpLq.SmallP.FEA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_le_of_gt (lt_of_lt_of_le hσ (norm_nonneg _))

theorem zero_measurements {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ)
    (b : Fin 0 → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) :
    SparseLpLq.SmallP.FEA A b σ 1 = Set.univ := by
  ext x
  simp [SparseLpLq.SmallP.FEA, qNorm_one, hσ]

theorem positive_sign_alone_insufficient :
    ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ => (-2 : ℝ)) ≤ 1) ∧
    ¬ ((∑ i : Fin 1, |(fun _ : Fin 1 => (-2 : ℝ)) i|) ≤ 1) := by
  norm_num [dotProduct]
end Queelius.SparseHalfspaces.Controls

end
