-- Prove2me | solution 1 for TVSDP.PolyOpt.min_eig_perturb
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:46:27.353851+00:00
-- url     : https://prove2.me/submissions/9ca78571-48ac-4e66-bd4e-3165b2ad7c82

import Mathlib

set_option autoImplicit false

open Filter Matrix

attribute [local instance] Matrix.normedAddCommGroup

lemma quad_bound_aux {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ i j, |D i j| ≤ δ) (x : Fin m → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ δ * m * (x ⬝ᵥ x) := by
  have h1 : x ⬝ᵥ (D *ᵥ x) = ∑ i, ∑ j, x i * D i j * x j := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1]
  calc |∑ i, ∑ j, x i * D i j * x j|
      ≤ ∑ i, |∑ j, x i * D i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * D i j * x j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, δ * ((x i ^ 2 + x j ^ 2) / 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h2 : |x i * D i j * x j| = |x i| * |D i j| * |x j| := by
          rw [abs_mul, abs_mul]
        rw [h2]
        have h3 : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
          have := sq_abs (x i); have := sq_abs (x j)
          nlinarith [sq_nonneg (|x i| - |x j|)]
        calc |x i| * |D i j| * |x j| = |D i j| * (|x i| * |x j|) := by ring
          _ ≤ δ * ((x i ^ 2 + x j ^ 2) / 2) :=
              mul_le_mul (hD i j) h3 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hδ
    _ = δ * m * (x ⬝ᵥ x) := by
        have hxx : x ⬝ᵥ x = ∑ j, x j ^ 2 := by simp [dotProduct, sq]
        have hi : ∀ i, ∑ j, δ * ((x i ^ 2 + x j ^ 2) / 2)
            = δ * ((m * x i ^ 2 + (x ⬝ᵥ x)) / 2) := by
          intro i
          rw [hxx, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
          simp
        simp only [hi]
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← hxx]
        simp
        ring

theorem solution {m : ℕ} (β : ℝ) (hβ : 0 < β) (G : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (H : ℕ → ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hG : ∀ t ∈ Set.Icc (0:ℝ) 1, (G t - β • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (hH : ∀ v : ℕ, ∀ t ∈ Set.Icc (0:ℝ) 1, (H v t).IsSymm)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, ‖G t - H v t‖ ≤ δ) :
    ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (H v t - (β / 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  have hδ : 0 < β / (2 * (m + 1)) := by positivity
  filter_upwards [hconv _ hδ] with v hv t ht
  have hsymm : (H v t - (β / 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact (hH v t ht).sub (by simp [Matrix.IsSymm, Matrix.transpose_smul])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm fun x => ?_
  have hD : ∀ i j, |(G t - H v t) i j| ≤ β / (2 * (m + 1)) := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm (G t - H v t)).trans (hv t ht)
  have hb := quad_bound_aux _ _ hδ.le hD x
  have hg := (hG t ht).dotProduct_mulVec_nonneg x
  simp only [star_trivial] at hg ⊢
  have hxx : 0 ≤ x ⬝ᵥ x := dotProduct_self_star_nonneg (v := x)
  have e : x ⬝ᵥ ((H v t - (β / 2) • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x)
      = x ⬝ᵥ ((G t - β • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x) + (β / 2) * (x ⬝ᵥ x)
        - x ⬝ᵥ ((G t - H v t) *ᵥ x) := by
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    ring
  rw [e]
  have hm : (β / (2 * (m + 1))) * m ≤ β / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have h4 : x ⬝ᵥ ((G t - H v t) *ᵥ x) ≤ β / (2 * (m + 1)) * m * (x ⬝ᵥ x) :=
    (le_abs_self _).trans hb
  have h5 : (β / (2 * (m + 1))) * m * (x ⬝ᵥ x) ≤ β / 2 * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right hm hxx
  linarith
