-- Prove2me | solution 1 for Weinberg1965.gravitonIndex_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T03:52:34.575021+00:00
-- url     : https://prove2.me/submissions/0c1cb22d-2af8-43b5-96f0-866d14460d13

import Mathlib
import Definitions.Def_Weinberg1965_Defs

open Weinberg1965

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W6_Weinberg1965_G_energy_gt (m : ℝ) (hm : 0 < m) (p u : Vec3) (hu : ‖u‖ = 1) :
    0 < energy m p - inner ℝ p u := by
  have h1 : inner ℝ p u ≤ ‖p‖ := by
    have := real_inner_le_norm p u
    rw [hu, mul_one] at this
    exact this
  have h2 : ‖p‖ < energy m p := by
    unfold energy
    rw [show ‖p‖ = Real.sqrt (‖p‖ ^ 2) from (Real.sqrt_sq (norm_nonneg p)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    have := pow_pos hm 2
    rw [Real.sq_sqrt (by positivity)]
    linarith
  linarith

theorem W6_Weinberg1965_G_pair (x y u : Vec3) (hxu : inner ℝ x u = 0) (hyu : inner ℝ y u = 0)
    (hu : ‖u‖ = 1) :
    ∑ i : Fin 3, ∑ j : Fin 3,
      (x i * x j - 1 / 2 * ‖x‖ ^ 2 * ((if i = j then 1 else 0) - u i * u j)) *
        (y i * y j - 1 / 2 * ‖y‖ ^ 2 * ((if i = j then 1 else 0) - u i * u j)) =
      (inner ℝ x y) ^ 2 - 1 / 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hu2 : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  rw [← real_inner_self_eq_norm_sq x, ← real_inner_self_eq_norm_sq y]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three] at hxu hyu hu2 ⊢
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false]
  linear_combination
    (1 / 2 * (y 0 * y 0 + y 1 * y 1 + y 2 * y 2) * (u 0 * x 0 + u 1 * x 1 + u 2 * x 2)) * hxu +
    (1 / 2 * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) * (u 0 * y 0 + u 1 * y 1 + u 2 * y 2)) * hyu +
    (1 / 4 * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) * (y 0 * y 0 + y 1 * y 1 + y 2 * y 2) *
      (u 0 * u 0 + u 1 * u 1 + u 2 * u 2 - 1)) * hu2

theorem W6_Weinberg1965_G_alg (ηn ηk En Ek αn αk Xnk Yn Yk mn mk : ℝ)
    (han : En - αn ≠ 0) (hak : Ek - αk ≠ 0)
    (hmn : mn ^ 2 = En ^ 2 - Yn - αn ^ 2) (hmk : mk ^ 2 = Ek ^ 2 - Yk - αk ^ 2) :
    ηn * ηk * ((Xnk + αn * αk - En * Ek) ^ 2 - 1 / 2 * mn ^ 2 * mk ^ 2) /
        ((En - αn) * (Ek - αk)) =
      ηn / (En - αn) * (ηk / (Ek - αk)) * (Xnk ^ 2 - 1 / 2 * Yn * Yk) +
      ηn * (-(ηk / (Ek - αk) * (Ek + αk) * Xnk) +
        1 / 4 * (En - αn) * (ηk / (Ek - αk)) * (Ek + αk) ^ 2 +
        1 / 2 * (En + αn) * (ηk / (Ek - αk)) * Yk) +
      ηk * (-(ηn / (En - αn) * (En + αn) * Xnk) +
        1 / 4 * (Ek - αk) * (ηn / (En - αn)) * (En + αn) ^ 2 +
        1 / 2 * (Ek + αk) * (ηn / (En - αn)) * Yn) := by
  rw [hmn, hmk]
  field_simp
  ring

theorem W6_Weinberg1965_gravitonAngular_nonneg {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ)
    (hG : 0 < G) (hm : ∀ n, 0 < m n)
    (hmom : ∑ n, η n • p n = 0)
    (henergy : ∑ n, η n * energy (m n) (p n) = 0) (u : Vec3) (hu : ‖u‖ = 1) :
    0 ≤ gravitonAngular G m p η u := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have ha : ∀ n, energy (m n) (p n) - inner ℝ (p n) u ≠ 0 := fun n =>
    (W6_Weinberg1965_G_energy_gt (m n) (hm n) (p n) u hu).ne'
  -- transverse parts
  have hxu : ∀ n, inner ℝ (p n - inner ℝ (p n) u • u) u = 0 := by
    intro n
    rw [inner_sub_left, real_inner_smul_left, huu]; ring
  have hX : ∀ n k, inner ℝ (p n) (p k) =
      inner ℝ (p n - inner ℝ (p n) u • u) (p k - inner ℝ (p k) u • u) +
        inner ℝ (p n) u * inner ℝ (p k) u := by
    intro n k
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, huu,
      real_inner_comm (p k) u, real_inner_comm (p n) u]
    ring
  have hm2 : ∀ n, m n ^ 2 = energy (m n) (p n) ^ 2 - ‖p n - inner ℝ (p n) u • u‖ ^ 2 -
      inner ℝ (p n) u ^ 2 := by
    intro n
    have hE : energy (m n) (p n) ^ 2 = ‖p n‖ ^ 2 + m n ^ 2 := by
      unfold energy; rw [Real.sq_sqrt (by positivity)]
    have hpp := hX n n
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hpp
    rw [hE, hpp]; ring
  have hηα : ∑ n, η n * inner ℝ (p n) u = 0 := by
    have h1 : inner ℝ (∑ n, η n • p n) u = ∑ n, η n * inner ℝ (p n) u := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun n _ => real_inner_smul_left _ _ _
    rw [← h1, hmom, inner_zero_left]
  have hηa : ∑ n, η n * (energy (m n) (p n) - inner ℝ (p n) u) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, henergy, hηα, sub_zero]
  have hηb : ∑ n, η n * (energy (m n) (p n) + inner ℝ (p n) u) = 0 := by
    simp only [mul_add, Finset.sum_add_distrib, henergy, hηα, add_zero]
  have hsx : ∑ n, η n • (p n - inner ℝ (p n) u • u) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, hmom, hηα,
      zero_smul, sub_zero]
  have hXsum : ∀ k, ∑ n, η n * inner ℝ (p n - inner ℝ (p n) u • u) (p k - inner ℝ (p k) u • u) = 0 := by
    intro k
    have h1 : inner ℝ (∑ n, η n • (p n - inner ℝ (p n) u • u)) (p k - inner ℝ (p k) u • u) =
        ∑ n, η n * inner ℝ (p n - inner ℝ (p n) u • u) (p k - inner ℝ (p k) u • u) := by
      rw [sum_inner]
      exact Finset.sum_congr rfl fun n _ => real_inner_smul_left _ _ _
    rw [← h1, hsx, inner_zero_left]
  -- the pointwise decomposition
  let E : ι → ℝ := fun n => energy (m n) (p n)
  let α : ι → ℝ := fun n => inner ℝ (p n) u
  let x : ι → Vec3 := fun n => p n - inner ℝ (p n) u • u
  let c : ι → ℝ := fun n => η n / (E n - α n)
  let L : ι → ι → ℝ := fun n k => -(c k * (E k + α k) * inner ℝ (x n) (x k)) +
        1 / 4 * (E n - α n) * c k * (E k + α k) ^ 2 + 1 / 2 * (E n + α n) * c k * ‖x k‖ ^ 2
  have hdec : ∀ n k, η n * η k *
      ((mdot (m n) (p n) (m k) (p k)) ^ 2 - (1 / 2) * m n ^ 2 * m k ^ 2) /
      ((energy (m n) (p n) - inner ℝ (p n) u) * (energy (m k) (p k) - inner ℝ (p k) u)) =
      c n * c k * (inner ℝ (x n) (x k) ^ 2 - 1 / 2 * ‖x n‖ ^ 2 * ‖x k‖ ^ 2) +
        η n * L n k + η k * L k n := by
    intro n k
    have hsym : inner ℝ (x k) (x n) = inner ℝ (x n) (x k) := real_inner_comm _ _
    simp only [L, hsym]
    unfold mdot
    rw [hX n k]
    exact W6_Weinberg1965_G_alg (η n) (η k) (E n) (E k) (α n) (α k) (inner ℝ (x n) (x k))
      (‖x n‖ ^ 2) (‖x k‖ ^ 2) (m n) (m k) (ha n) (ha k) (hm2 n) (hm2 k)
  have hL0 : ∀ k, ∑ n, η n * L n k = 0 := by
    intro k
    have e : ∑ n, η n * L n k =
        -(c k * (E k + α k)) * (∑ n, η n * inner ℝ (x n) (x k)) +
        1 / 4 * c k * (E k + α k) ^ 2 * (∑ n, η n * (E n - α n)) +
        1 / 2 * c k * ‖x k‖ ^ 2 * (∑ n, η n * (E n + α n)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [L]
      ring
    rw [e, hXsum k, hηa, hηb]
    ring
  -- the main quadratic form is a sum of squares
  let F : ι → Fin 3 → Fin 3 → ℝ := fun n i j =>
    x n i * x n j - 1 / 2 * ‖x n‖ ^ 2 * ((if i = j then 1 else 0) - u i * u j)
  have hmain : ∑ n, ∑ k, c n * c k * (inner ℝ (x n) (x k) ^ 2 - 1 / 2 * ‖x n‖ ^ 2 * ‖x k‖ ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, (∑ n, c n * F n i j) ^ 2 := by
    have h1 : ∀ i j, (∑ n, c n * F n i j) ^ 2 = ∑ n, ∑ k, c n * c k * (F n i j * F k i j) := by
      intro i j
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    simp_rw [h1]
    have h2 : ∀ n k, inner ℝ (x n) (x k) ^ 2 - 1 / 2 * ‖x n‖ ^ 2 * ‖x k‖ ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, F n i j * F k i j := fun n k =>
      (W6_Weinberg1965_G_pair (x n) (x k) u (hxu n) (hxu k) hu).symm
    simp_rw [h2, Finset.mul_sum]
    calc ∑ n, ∑ k, ∑ i : Fin 3, ∑ j : Fin 3, c n * c k * (F n i j * F k i j)
        = ∑ n, ∑ i : Fin 3, ∑ k, ∑ j : Fin 3, c n * c k * (F n i j * F k i j) :=
          Finset.sum_congr rfl fun n _ => Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ n, ∑ k, ∑ j : Fin 3, c n * c k * (F n i j * F k i j) := Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ n, ∑ j : Fin 3, ∑ k, c n * c k * (F n i j * F k i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ n, ∑ k, c n * c k * (F n i j * F k i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have htot : ∑ n, ∑ k, η n * η k *
      ((mdot (m n) (p n) (m k) (p k)) ^ 2 - (1 / 2) * m n ^ 2 * m k ^ 2) /
      ((energy (m n) (p n) - inner ℝ (p n) u) * (energy (m k) (p k) - inner ℝ (p k) u)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (∑ n, c n * F n i j) ^ 2 := by
    simp_rw [hdec, Finset.sum_add_distrib]
    rw [hmain]
    have hA : ∑ n, ∑ k, η n * L n k = 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun k _ => hL0 k
    have hB : ∑ n, ∑ k, η k * L k n = 0 := Finset.sum_eq_zero fun n _ => hL0 n
    rw [hA, hB]
    ring
  unfold gravitonAngular
  rw [htot]
  have hK : 0 ≤ 8 * Real.pi * G / (2 * (2 * Real.pi) ^ 3) := by positivity
  exact mul_nonneg hK (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem solution {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ)
    (hG : 0 < G) (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hmom : ∑ n, η n • p n = 0)
    (henergy : ∑ n, η n * energy (m n) (p n) = 0) :
    0 ≤ gravitonIndex G m p η := by
  unfold gravitonIndex solidAngleIntegral
  refine MeasureTheory.integral_nonneg fun u => ?_
  exact W6_Weinberg1965_gravitonAngular_nonneg G m p η hG hm hmom henergy (u : Vec3) (by simp)
