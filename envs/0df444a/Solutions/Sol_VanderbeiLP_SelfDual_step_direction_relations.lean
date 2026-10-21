-- Prove2me | solution 1 for VanderbeiLP.SelfDual.step_direction_relations
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:09:15.419989+00:00
-- url     : https://prove2.me/submissions/c87cceb5-50ce-468d-b9f2-f6ae36dad9c5

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

set_option autoImplicit false
open Matrix VanderbeiLP.SelfDual

theorem skew_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = -((A *ᵥ u) ⬝ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, Matrix.neg_mulVec,
    neg_dotProduct]

theorem skew_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (v : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ v) = 0 := by
  have h := skew_swap A hA v v
  rw [dotProduct_comm (A *ᵥ v) v] at h
  linarith

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x z dx dz : Fin n → ℝ) (hstep : IsStepDirection A δ x z dx dz) (θ : ℝ) :
    dz ⬝ᵥ dx = 0 ∧
    rho A (x + θ • dx) (z + θ • dz) = (1 - θ + θ * δ) • rho A x z ∧
    mu (x + θ • dx) (z + θ • dz) = (1 - θ + θ * δ) * mu x z ∧
    centralityResidual (x + θ • dx) (z + θ • dz) =
      (1 - θ) • centralityResidual x z + θ ^ 2 • (fun j => dx j * dz j) := by
  obtain ⟨h1, h2⟩ := hstep
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact this.ne'
  have hnmu : (n : ℝ) * mu x z = x ⬝ᵥ z := by
    unfold mu; field_simp
  -- sum of the second equation
  have hsum : z ⬝ᵥ dx + x ⬝ᵥ dz = δ * (x ⬝ᵥ z) - x ⬝ᵥ z := by
    have : ∑ j, (z j * dx j + x j * dz j) = ∑ j, (δ * mu x z - x j * z j) :=
      Finset.sum_congr rfl (fun j _ => h2 j)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    unfold dotProduct at hnmu ⊢
    rw [this]
    linear_combination δ * hnmu
  have hdz : dz = (-(1 - δ)) • rho A x z - A *ᵥ dx := eq_sub_of_add_eq' h1
  have hxrho : x ⬝ᵥ rho A x z = x ⬝ᵥ z := by
    unfold rho; rw [dotProduct_add, skew_quad A hA, zero_add]
  have hxdz : x ⬝ᵥ dz = -(1 - δ) * (x ⬝ᵥ z) + (A *ᵥ x) ⬝ᵥ dx := by
    rw [hdz, dotProduct_sub, dotProduct_smul, smul_eq_mul, hxrho, skew_swap A hA x dx]
    ring
  have hrho : rho A x z ⬝ᵥ dx = 0 := by
    unfold rho
    rw [add_dotProduct]
    rw [hxdz] at hsum
    linarith
  have hdd : dz ⬝ᵥ dx = 0 := by
    rw [hdz, sub_dotProduct, smul_dotProduct, smul_eq_mul, hrho, dotProduct_comm (A *ᵥ dx) dx,
      skew_quad A hA]
    ring
  have hmu : mu (x + θ • dx) (z + θ • dz) = (1 - θ + θ * δ) * mu x z := by
    have e : (x + θ • dx) ⬝ᵥ (z + θ • dz) =
        x ⬝ᵥ z + θ * (z ⬝ᵥ dx + x ⬝ᵥ dz) + θ ^ 2 * (dz ⬝ᵥ dx) := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
        dotProduct_smul, dotProduct_smul, dotProduct_comm dx z, dotProduct_comm dx dz]
      simp only [smul_eq_mul]
      ring
    unfold mu
    rw [e, hsum, hdd]
    ring
  refine ⟨hdd, ?_, hmu, ?_⟩
  · have e : rho A (x + θ • dx) (z + θ • dz) = rho A x z + θ • (A *ᵥ dx + dz) := by
      unfold rho
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      module
    rw [e, h1]
    module
  · funext j
    simp only [centralityResidual, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hmu]
    linear_combination θ * (h2 j)
