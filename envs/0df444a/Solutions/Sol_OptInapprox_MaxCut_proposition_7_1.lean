-- Prove2me | solution 1 for OptInapprox.MaxCut.proposition_7_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:14:02.776801+00:00
-- url     : https://prove2.me/submissions/4a470498-05c0-49e6-a256-4bcff915e6dd

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

open OptInapprox.MaxCut

lemma corrKernel_eq_sum_chi {n : ℕ} (ρ : ℝ) (x y : Fin n → Bool) :
    corrKernel ρ x y =
      (2 ^ n : ℝ)⁻¹ * ∑ S : Finset (Fin n), ρ ^ S.card * (chi S x * chi S y) := by
  unfold corrKernel
  have h1 : (∏ i : Fin n, (1 + ρ * pm (x i) * pm (y i)) / 2) =
      (2 ^ n : ℝ)⁻¹ * ∏ i : Fin n, (ρ * (pm (x i) * pm (y i)) + 1) := by
    have hdiv : ∀ i : Fin n, (1 + ρ * pm (x i) * pm (y i)) / 2 =
        (2 : ℝ)⁻¹ * (ρ * (pm (x i) * pm (y i)) + 1) := fun i => by ring
    simp_rw [hdiv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, inv_pow]
  rw [h1]
  congr 1
  rw [Finset.prod_add]
  have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext S; simp
  rw [hpow]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp [chi, Finset.prod_mul_distrib, Finset.prod_const]

lemma fourier_sq {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier f S ^ 2 =
      ((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y * (chi S x * chi S y) := by
  unfold OptInapprox.MaxCut.fourier cubeE
  have h1 : (∑ x, f x * chi S x) * (∑ y, f y * chi S y) =
      ∑ x, ∑ y, f x * f y * (chi S x * chi S y) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    ring
  calc ((2 ^ n : ℝ)⁻¹ * ∑ x, f x * chi S x) ^ 2
      = ((2 ^ n : ℝ)⁻¹) ^ 2 * ((∑ x, f x * chi S x) * (∑ y, f y * chi S y)) := by ring
    _ = ((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y * (chi S x * chi S y) := by rw [h1]

theorem solution {n : ℕ} (f : (Fin n → Bool) → ℝ) (ρ : ℝ) (hρ₁ : -1 ≤ ρ) (hρ₂ : ρ ≤ 1) :
    noiseStab ρ f = cubeE (fun x => f x * bonamiBeckner ρ f x) ∧
      noiseStab ρ f = ∑ S : Finset (Fin n), ρ ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2 := by
  refine ⟨?_, ?_⟩
  · unfold noiseStab bonamiBeckner cubeE
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  · have hrhs : ∑ S : Finset (Fin n), ρ ^ S.card * OptInapprox.MaxCut.fourier f S ^ 2 =
        ((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y *
          (∑ S : Finset (Fin n), ρ ^ S.card * (chi S x * chi S y)) := by
      simp_rw [fourier_sq]
      trans ∑ S : Finset (Fin n),
        (((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y * (ρ ^ S.card * (chi S x * chi S y)))
      · refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [← mul_assoc, mul_comm (ρ ^ S.card), mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
      · rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
    rw [hrhs]
    unfold noiseStab cubeE
    simp_rw [corrKernel_eq_sum_chi]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
