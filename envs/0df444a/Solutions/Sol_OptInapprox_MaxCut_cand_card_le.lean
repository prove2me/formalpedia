-- Prove2me | solution 1 for OptInapprox.MaxCut.cand_card_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:14:03.714822+00:00
-- url     : https://prove2.me/submissions/4d3d9c37-ece0-4dbc-bfe2-7b0830f375f3

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

open OptInapprox.MaxCut

lemma pm_mul_self (b : Bool) : pm b * pm b = 1 := by
  cases b <;> norm_num [pm]

lemma pm_mul_eq_neg_one_of_ne {b₁ b₂ : Bool} (h : b₁ ≠ b₂) : pm b₁ * pm b₂ = -1 := by
  cases b₁ <;> cases b₂
  · contradiction
  · norm_num [pm]
  · norm_num [pm]
  · contradiction

lemma sum_chi_mul_chi {n : ℕ} (x z : Fin n → Bool) :
    ∑ S : Finset (Fin n), chi S x * chi S z = if x = z then (2 : ℝ) ^ n else 0 := by
  have hprod : ∏ j ∈ (Finset.univ : Finset (Fin n)), (pm (x j) * pm (z j) + 1) =
      ∑ S : Finset (Fin n), chi S x * chi S z := by
    rw [Finset.prod_add]
    have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
      ext S; simp
    rw [hpow]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    simp [chi, Finset.prod_mul_distrib]
  rw [← hprod]
  by_cases hxz : x = z
  · subst hxz
    rw [if_pos rfl]
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin n)), pm (x j) * pm (x j) + 1 = (2 : ℝ) := by
      intro j _
      rw [pm_mul_self]
      norm_num
    rw [Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hxz]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxz
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [pm_mul_eq_neg_one_of_ne hj]
    ring

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

lemma parseval_cube {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 = cubeE (fun x => f x ^ 2) := by
  have hrhs : ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 =
      ((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y * (∑ S : Finset (Fin n), chi S x * chi S y) := by
    simp_rw [fourier_sq, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum]
  rw [hrhs]
  simp_rw [sum_chi_mul_chi]
  have hinner : ∀ x : Fin n → Bool,
      ∑ y : Fin n → Bool, f x * f y * (if x = y then (2 : ℝ) ^ n else 0) =
      (2 : ℝ) ^ n * f x ^ 2 := by
    intro x
    have h1 : ∀ y : Fin n → Bool,
        f x * f y * (if x = y then (2 : ℝ) ^ n else 0) =
        if y = x then (2 : ℝ) ^ n * (f x * f y) else 0 := by
      intro y
      simp only [eq_comm (a := x) (b := y)]
      split_ifs <;> ring
    simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp_rw [hinner, ← Finset.mul_sum]
  unfold cubeE
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [h2n]

lemma sum_fourier_sq_le_one {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2 ≤ 1 := by
  rw [parseval_cube]
  unfold cubeE
  have hle : ∑ x : Fin n → Bool, f x ^ 2 ≤ ∑ _x : Fin n → Bool, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hfx : |f x| ^ 2 ≤ 1 ^ 2 := sq_le_sq.mpr (by simpa using hf x)
    simpa [sq_abs] using hfx
  have hsum1 : ∑ _x : Fin n → Bool, (1 : ℝ) = (2 : ℝ) ^ n := by
    simp [Finset.card_univ, Fintype.card_fin]
  have hpos : (0 : ℝ) ≤ (2 ^ n : ℝ)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left (hle.trans_eq hsum1) hpos
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rwa [inv_mul_cancel₀ h2n] at hmul

theorem solution {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (k : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    ∑ i, lowDegInf k i f ≤ k ∧
      ((Finset.univ.filter fun i => δ / 2 ≤ lowDegInf k i f).card : ℝ) ≤ 2 * k / δ := by
  have hsum_le : ∑ i, lowDegInf k i f ≤ k := by
    unfold lowDegInf
    have hswap : ∑ i : Fin n,
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ S.card ≤ k),
            OptInapprox.MaxCut.fourier f S ^ 2 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
          (S.card : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      by_cases hSk : S.card ≤ k
      · simp only [hSk, and_true, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, if_true]
      · simp [hSk]
    rw [hswap]
    have hstep1 : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
          (S.card : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 ≤
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
          (k : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 := by
      refine Finset.sum_le_sum (fun S hS => ?_)
      have hSk : (S.card : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hS).2
      exact mul_le_mul_of_nonneg_right hSk (sq_nonneg _)
    have hstep2 : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
          (k : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 ≤
        ∑ S : Finset (Fin n), (k : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 := by
      refine Finset.sum_le_univ_sum_of_nonneg (fun S => ?_)
      positivity
    have hstep3 : ∑ S : Finset (Fin n), (k : ℝ) * OptInapprox.MaxCut.fourier f S ^ 2 ≤ k := by
      rw [← Finset.mul_sum]
      calc (k : ℝ) * ∑ S : Finset (Fin n), OptInapprox.MaxCut.fourier f S ^ 2
          ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left (sum_fourier_sq_le_one f hf) (Nat.cast_nonneg k)
        _ = k := mul_one _
    exact (hstep1.trans hstep2).trans hstep3
  refine ⟨hsum_le, ?_⟩
  let Cand := Finset.univ.filter (fun i : Fin n => δ / 2 ≤ lowDegInf k i f)
  have hmarkov : (Cand.card : ℝ) * (δ / 2) ≤ ∑ i : Fin n, lowDegInf k i f := by
    calc (Cand.card : ℝ) * (δ / 2)
        = ∑ _i ∈ Cand, (δ / 2) := by simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ Cand, lowDegInf k i f := by
          refine Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i : Fin n, lowDegInf k i f := by
          refine Finset.sum_le_univ_sum_of_nonneg (fun i => ?_)
          unfold lowDegInf
          exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  have hle : (Cand.card : ℝ) * (δ / 2) ≤ k := hmarkov.trans hsum_le
  rw [le_div_iff₀ hδ]
  linarith
