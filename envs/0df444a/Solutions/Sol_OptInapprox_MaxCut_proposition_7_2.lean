-- Prove2me | solution 1 for OptInapprox.MaxCut.proposition_7_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:09:35.027337+00:00
-- url     : https://prove2.me/submissions/5c24d2a7-4eb7-4d8b-8eb8-ddcce55f3bb6

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

open OptInapprox.MaxCut

def flipCoord {n : ℕ} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp]
lemma flipCoord_involutive {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    flipCoord i (flipCoord i x) = x := by
  ext j
  unfold flipCoord
  by_cases h : j = i
  · subst h; simp
  · simp [h]

def flipEquiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := flipCoord i
  invFun := flipCoord i
  left_inv := flipCoord_involutive i
  right_inv := flipCoord_involutive i

lemma pm_not (b : Bool) : pm (!b) = -pm b := by
  cases b <;> norm_num [pm]

lemma pm_mul_self (b : Bool) : pm b * pm b = 1 := by
  cases b <;> norm_num [pm]

lemma pm_mul_eq_neg_one_of_ne {b₁ b₂ : Bool} (h : b₁ ≠ b₂) : pm b₁ * pm b₂ = -1 := by
  cases b₁ <;> cases b₂
  · contradiction
  · norm_num [pm]
  · norm_num [pm]
  · contradiction

lemma chi_flipCoord {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (y : Fin n → Bool) :
    chi S (flipCoord i y) = if i ∈ S then -chi S y else chi S y := by
  unfold chi
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    rw [← Finset.mul_prod_erase S (fun j => pm (flipCoord i y j)) hi]
    rw [← Finset.mul_prod_erase S (fun j => pm (y j)) hi]
    have h1 : pm (flipCoord i y i) = -pm (y i) := by
      simp [flipCoord, pm_not]
    have h2 : ∏ j ∈ S.erase i, pm (flipCoord i y j) = ∏ j ∈ S.erase i, pm (y j) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp [flipCoord, hne]
    rw [h1, h2, neg_mul]
  · rw [if_neg hi]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hne : j ≠ i := fun h => hi (h ▸ hj)
    simp [flipCoord, hne]

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

lemma sum_filter_chi_mul_chi {n : ℕ} (i : Fin n) (x y : Fin n → Bool) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), chi S x * chi S y =
      ((if x = y then (2 : ℝ) ^ n else 0) - (if x = flipCoord i y then (2 : ℝ) ^ n else 0)) / 2 := by
  have hdiff : ∑ S : Finset (Fin n), (chi S x * chi S y - chi S x * chi S (flipCoord i y)) =
      2 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), chi S x * chi S y := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [chi_flipCoord]
    split_ifs <;> ring
  rw [Finset.sum_sub_distrib, sum_chi_mul_chi, sum_chi_mul_chi] at hdiff
  linarith

lemma coordVar_eq_flip {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    coordVar i f x = ((f x - f (flipCoord i x)) / 2) ^ 2 := by
  unfold coordVar flipCoord
  rw [Fintype.sum_bool, Fintype.sum_bool]
  cases hxi : x i
  · have h1 : Function.update x i false = x := Function.update_eq_self_iff.mpr hxi.symm
    simp only [h1, Bool.not_false]
    ring
  · have h1 : Function.update x i true = x := Function.update_eq_self_iff.mpr hxi.symm
    simp only [h1, Bool.not_true]
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

theorem solution {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence i f = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      OptInapprox.MaxCut.fourier f S ^ 2 := by
  have hrhs : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
        OptInapprox.MaxCut.fourier f S ^ 2 =
      ((2 ^ n : ℝ)⁻¹) ^ 2 * ∑ x, ∑ y, f x * f y *
        (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), chi S x * chi S y) := by
    simp_rw [fourier_sq, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum]
  rw [hrhs]
  simp_rw [sum_filter_chi_mul_chi]
  have hinner : ∀ x : Fin n → Bool,
      ∑ y : Fin n → Bool, f x * f y *
        (((if x = y then (2 : ℝ) ^ n else 0) - (if x = flipCoord i y then (2 : ℝ) ^ n else 0)) / 2) =
      (2 : ℝ) ^ n * (f x * (f x - f (flipCoord i x)) / 2) := by
    intro x
    have h1 : ∀ y : Fin n → Bool,
        f x * f y * (((if x = y then (2 : ℝ) ^ n else 0) - (if x = flipCoord i y then (2 : ℝ) ^ n else 0)) / 2) =
        (if y = x then (2 : ℝ) ^ n * (f x * f y / 2) else 0) -
        (if y = flipCoord i x then (2 : ℝ) ^ n * (f x * f y / 2) else 0) := by
      intro y
      have heq : (x = flipCoord i y) ↔ (y = flipCoord i x) := by
        constructor
        · rintro rfl; rw [flipCoord_involutive]
        · rintro rfl; rw [flipCoord_involutive]
      simp only [eq_comm (a := x) (b := y), heq]
      split_ifs <;> ring
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp_rw [hinner, ← Finset.mul_sum]
  have hflip_sum : ∑ x : Fin n → Bool, f x * (f x - f (flipCoord i x)) / 2 =
      ∑ x : Fin n → Bool, ((f x - f (flipCoord i x)) / 2) ^ 2 := by
    have hbij : ∑ x : Fin n → Bool, f (flipCoord i x) * (f (flipCoord i x) - f (flipCoord i (flipCoord i x))) / 2 =
        ∑ x : Fin n → Bool, f x * (f x - f (flipCoord i x)) / 2 :=
      Equiv.sum_comp (flipEquiv i) (fun x => f x * (f x - f (flipCoord i x)) / 2)
    simp_rw [flipCoord_involutive] at hbij
    have hadd : (∑ x : Fin n → Bool, f x * (f x - f (flipCoord i x)) / 2) +
        (∑ x : Fin n → Bool, f (flipCoord i x) * (f (flipCoord i x) - f x) / 2) =
        2 * ∑ x : Fin n → Bool, ((f x - f (flipCoord i x)) / 2) ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      ring
    linarith
  rw [hflip_sum]
  unfold influence cubeE
  simp_rw [coordVar_eq_flip]
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [h2n]
