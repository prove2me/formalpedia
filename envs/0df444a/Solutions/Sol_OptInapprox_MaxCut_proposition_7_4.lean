-- Prove2me | solution 1 for OptInapprox.MaxCut.proposition_7_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:45.407718+00:00
-- url     : https://prove2.me/submissions/11f225fb-1c27-4e32-bf0d-9436d6e8aecc

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_1
import Theorems.Thm_OptInapprox_MaxCut_proposition_7_2

open OptInapprox.MaxCut

noncomputable section

private def negCube {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !x i

@[simp]
private lemma negCube_involutive {n : ℕ} (x : Fin n → Bool) : negCube (negCube x) = x := by
  ext i
  simp [negCube]

private def negCubeEquiv {n : ℕ} : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := negCube
  invFun := negCube
  left_inv := negCube_involutive
  right_inv := negCube_involutive

private lemma pm_not (b : Bool) : pm (!b) = -pm b := by
  cases b <;> norm_num [pm]

private lemma chi_negCube {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S (negCube x) = (-1 : ℝ) ^ S.card * chi S x := by
  unfold chi negCube
  have h : ∀ i ∈ S, pm (!x i) = (-1 : ℝ) * pm (x i) := by
    intro i _
    rw [pm_not]
    ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const]

private def oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (f x - f (negCube x)) / 2

private lemma abs_oddPart_le_one {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (x : Fin n → Bool) : |oddPart f x| ≤ 1 := by
  unfold oddPart
  rw [abs_div, Nat.abs_ofNat]
  have h1 := hf x
  have h2 := hf (negCube x)
  have h3 := abs_sub (f x) (f (negCube x))
  linarith

private lemma cubeE_oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) : cubeE (oddPart f) = 0 := by
  unfold cubeE oddPart
  have hbij : ∑ x : Fin n → Bool, f (negCube x) = ∑ x : Fin n → Bool, f x :=
    Equiv.sum_comp negCubeEquiv f
  have hsum : ∑ x : Fin n → Bool, (f x - f (negCube x)) / 2 =
      ((∑ x, f x) - (∑ x, f (negCube x))) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsum, hbij]
  ring

private lemma fourier_negCube {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (fun x => f (negCube x)) S =
      (-1 : ℝ) ^ S.card * OptInapprox.MaxCut.fourier f S := by
  unfold OptInapprox.MaxCut.fourier cubeE
  have hbij : ∑ x : Fin n → Bool, f (negCube x) * chi S x =
      ∑ y : Fin n → Bool, f y * chi S (negCube y) := by
    have h := Equiv.sum_comp negCubeEquiv (fun x => f (negCube x) * chi S x)
    rw [← h]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    change f (negCube (negCube y)) * chi S (negCube y) = f y * chi S (negCube y)
    rw [negCube_involutive]
  rw [hbij]
  simp_rw [chi_negCube]
  have h2 : ∑ y : Fin n → Bool, f y * ((-1 : ℝ) ^ S.card * chi S y) =
      (-1 : ℝ) ^ S.card * ∑ y : Fin n → Bool, f y * chi S y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [h2]
  ring

private lemma fourier_oddPart {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (oddPart f) S =
      ((1 - (-1 : ℝ) ^ S.card) / 2) * OptInapprox.MaxCut.fourier f S := by
  have hlin : OptInapprox.MaxCut.fourier (oddPart f) S =
      (OptInapprox.MaxCut.fourier f S -
        OptInapprox.MaxCut.fourier (fun x => f (negCube x)) S) / 2 := by
    unfold OptInapprox.MaxCut.fourier cubeE oddPart
    have hsum : ∑ x : Fin n → Bool, (f x - f (negCube x)) / 2 * chi S x =
        ((∑ x, f x * chi S x) - (∑ x, f (negCube x) * chi S x)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    ring
  rw [hlin, fourier_negCube]
  ring

private lemma odd_coeff_sq_le_one (m : ℕ) : ((1 - (-1 : ℝ) ^ m) / 2) ^ 2 ≤ 1 := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow]; norm_num
  · rw [hm.neg_one_pow]; norm_num

private lemma neg_odd_pow_le (ρ : ℝ) (m : ℕ) :
    -((-ρ) ^ m * ((1 - (-1 : ℝ) ^ m) / 2) ^ 2) ≤ ρ ^ m := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow]
    have hpos : 0 ≤ ρ ^ m := hm.pow_nonneg ρ
    linarith
  · rw [hm.neg_one_pow, hm.neg_pow]
    linarith

private lemma fourier_oddPart_sq_le {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) :
    OptInapprox.MaxCut.fourier (oddPart f) S ^ 2 ≤ OptInapprox.MaxCut.fourier f S ^ 2 := by
  rw [fourier_oddPart, mul_pow]
  calc ((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2 * OptInapprox.MaxCut.fourier f S ^ 2
      ≤ 1 * OptInapprox.MaxCut.fourier f S ^ 2 :=
        mul_le_mul_of_nonneg_right (odd_coeff_sq_le_one S.card) (sq_nonneg _)
    _ = OptInapprox.MaxCut.fourier f S ^ 2 := one_mul _

private lemma influence_oddPart_le {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence i (oddPart f) ≤ influence i f := by
  rw [proposition_7_2 (oddPart f) i, proposition_7_2 f i]
  exact Finset.sum_le_sum (fun S _ => fourier_oddPart_sq_le f S)

private lemma neg_noiseStab_oddPart_le {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0) :
    -noiseStab (-ρ) (oddPart f) ≤ noiseStab ρ f := by
  rw [(proposition_7_1 (oddPart f) (-ρ) (by linarith) (by linarith)).2,
      (proposition_7_1 f ρ (by linarith) (by linarith)).2,
      ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun S _ => ?_)
  rw [fourier_oddPart, mul_pow]
  have h1 : -((-ρ) ^ S.card * (((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2 *
      OptInapprox.MaxCut.fourier f S ^ 2)) =
      (-((-ρ) ^ S.card * ((1 - (-1 : ℝ) ^ S.card) / 2) ^ 2)) *
        OptInapprox.MaxCut.fourier f S ^ 2 := by ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (neg_odd_pow_le ρ S.card) (sq_nonneg _)

end

theorem solution (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) →
        (∀ i, influence i f ≤ δ) → 1 - 2 / Real.pi * Real.arccos ρ - ε ≤ noiseStab ρ f := by
  obtain ⟨δ, hδ_pos, hδ⟩ := hMIS (-ρ) (by linarith) (by linarith) ε hε
  refine ⟨δ, hδ_pos, fun n f hf hinf => ?_⟩
  have hmis_g := hδ n (oddPart f) (abs_oddPart_le_one f hf) (cubeE_oddPart f)
    (fun i => (influence_oddPart_le f i).trans (hinf i))
  have hns := neg_noiseStab_oddPart_le f ρ hρ₀ hρ₁
  have harc : 1 - 2 / Real.pi * Real.arccos (-ρ) = -(1 - 2 / Real.pi * Real.arccos ρ) := by
    rw [Real.arccos_neg]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi]
    ring
  linarith
