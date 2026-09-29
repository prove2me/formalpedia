-- Prove2me | solution 1 for WeierstrassCurve.addX_self_sub_mul_sq_of_criticalCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/051547a3-1395-57d5-8ea7-a376a4dd3bb6

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace S04V

variable {K : Type*} [Field K] (A : ValuationSubring K)

local notation "v" => A.valuation

lemma mem_iff {z : K} : z ∈ A ↔ v z ≤ 1 := (A.valuation_le_one_iff z).symm

lemma le_one {z : K} (hz : z ∈ A) : v z ≤ 1 := (A.valuation_le_one_iff z).mpr hz

lemma mem {z : K} (hz : v z ≤ 1) : z ∈ A := (A.valuation_le_one_iff z).mp hz

lemma nonunit_iff {z : K} : z ∈ A.nonunits ↔ v z < 1 := A.mem_nonunits_iff

lemma intCast_mem' (n : ℤ) : (n : K) ∈ A := intCast_mem A n

lemma natCast_mem' (n : ℕ) : (n : K) ∈ A := natCast_mem A n

lemma intCast_le (n : ℤ) : v (n : K) ≤ 1 := le_one A (intCast_mem' A n)

lemma natCast_le (n : ℕ) : v (n : K) ≤ 1 := le_one A (natCast_mem' A n)

lemma ofNat_le (n : ℕ) [n.AtLeastTwo] : v (ofNat(n) : K) ≤ 1 := le_one A (ofNat_mem A n)

lemma add_lt_one {a b : K} (ha : v a < 1) (hb : v b < 1) : v (a + b) < 1 :=
  Valuation.map_add_lt _ ha hb

lemma sub_lt_one {a b : K} (ha : v a < 1) (hb : v b < 1) : v (a - b) < 1 := by
  rw [sub_eq_add_neg]; exact Valuation.map_add_lt _ ha (by rwa [Valuation.map_neg])

lemma add_le_one {a b : K} (ha : v a ≤ 1) (hb : v b ≤ 1) : v (a + b) ≤ 1 :=
  Valuation.map_add_le _ ha hb

lemma sub_le_one {a b : K} (ha : v a ≤ 1) (hb : v b ≤ 1) : v (a - b) ≤ 1 :=
  Valuation.map_sub_le _ ha hb

lemma mul_lt_one_of_le_of_lt {a b : K} (ha : v a ≤ 1) (hb : v b < 1) : v (a * b) < 1 := by
  rw [Valuation.map_mul]
  calc v a * v b ≤ 1 * v b := mul_le_mul' ha le_rfl
    _ = v b := one_mul _
    _ < 1 := hb

lemma mul_lt_one_of_lt_of_le {a b : K} (ha : v a < 1) (hb : v b ≤ 1) : v (a * b) < 1 := by
  rw [mul_comm]; exact mul_lt_one_of_le_of_lt A hb ha

lemma v_mul_le_one {a b : K} (ha : v a ≤ 1) (hb : v b ≤ 1) : v (a * b) ≤ 1 := by
  rw [Valuation.map_mul]; exact mul_le_one' ha hb

lemma v_pow_le_one {a : K} (ha : v a ≤ 1) (n : ℕ) : v (a ^ n) ≤ 1 := by
  rw [Valuation.map_pow]; exact pow_le_one₀ zero_le' ha

lemma add_eq_left {a b : K} (h : v b < v a) : v (a + b) = v a :=
  Valuation.map_add_eq_of_lt_left _ h

lemma add_eq_right {a b : K} (h : v a < v b) : v (a + b) = v b :=
  Valuation.map_add_eq_of_lt_right _ h

lemma sub_eq_left {a b : K} (h : v b < v a) : v (a - b) = v a := by
  rw [sub_eq_add_neg]; exact Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg])

lemma sub_eq_right {a b : K} (h : v a < v b) : v (a - b) = v b := by
  rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rwa [Valuation.map_neg]),
    Valuation.map_neg]

lemma unit_add_small {a b : K} (ha : v a = 1) (hb : v b < 1) : v (a + b) = 1 := by
  rw [add_eq_left A (by rwa [ha]), ha]

lemma small_add_unit {a b : K} (ha : v a < 1) (hb : v b = 1) : v (a + b) = 1 := by
  rw [add_comm]; exact unit_add_small A hb ha

lemma ne_zero_of_v_eq_one {a : K} (ha : v a = 1) : a ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at ha; exact zero_ne_one ha

lemma ne_zero_of_lt_v {a : K} {g : A.ValueGroup} (ha : g < v a) : a ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at ha; exact not_lt_zero ha

lemma eq_one_of_pow_eq_one {s : K} {n : ℕ} (hn : n ≠ 0) (h : v s ^ n = 1) : v s = 1 :=
  (pow_eq_one_iff_of_nonneg zero_le' hn).mp h

lemma lt_one_of_mul_lt_one_of_eq_one {a b : K} (h : v (a * b) < 1) (hb : v b = 1) : v a < 1 := by
  rwa [Valuation.map_mul, hb, mul_one] at h

lemma div_eq {a b : K} : v (a / b) = v a / v b := Valuation.map_div _ _ _

end S04V

theorem S04_res_quad
    {K : Type*} [Field K] (A : ValuationSubring K) {a b t₁ t₂ t₃ : K} (ha : a ∈ A) (hb : b ∈ A)
    (hdisc : A.valuation (a ^ 2 + 4 * b) = 1)
    (h₁ : t₁ ∈ A) (h₂ : t₂ ∈ A) (h₃ : t₃ ∈ A)
    (hr₁ : A.valuation (t₁ ^ 2 + a * t₁ - b) < 1) (hr₂ : A.valuation (t₂ ^ 2 + a * t₂ - b) < 1)
    (hr₃ : A.valuation (t₃ ^ 2 + a * t₃ - b) < 1)
    (h₁₂ : A.valuation (t₁ - t₂) = 1) (h₂₃ : A.valuation (t₂ - t₃) = 1) :
    A.valuation (t₁ - t₃) < 1 := by
  have _ := hdisc; have _ := ha; have _ := hb; have _ := h₂

  have hsum : A.valuation (t₁ + t₂ + a) < 1 := by
    have hid : (t₁ - t₂) * (t₁ + t₂ + a) = (t₁ ^ 2 + a * t₁ - b) - (t₂ ^ 2 + a * t₂ - b) := by ring
    have hlt : A.valuation ((t₁ - t₂) * (t₁ + t₂ + a)) < 1 := by
      rw [hid]; exact S04V.sub_lt_one A hr₁ hr₂
    rwa [Valuation.map_mul, h₁₂, one_mul] at hlt

  have hprod : A.valuation (t₁ * t₂ + b) < 1 := by
    have hid : t₁ * t₂ + b = t₁ * (t₁ + t₂ + a) - (t₁ ^ 2 + a * t₁ - b) := by ring
    rw [hid]
    exact S04V.sub_lt_one A (S04V.mul_lt_one_of_le_of_lt A (S04V.le_one A h₁) hsum) hr₁

  have hkey : A.valuation ((t₃ - t₁) * (t₃ - t₂)) < 1 := by
    have hid : (t₃ - t₁) * (t₃ - t₂) =
        (t₃ ^ 2 + a * t₃ - b) - t₃ * (t₁ + t₂ + a) + (t₁ * t₂ + b) := by ring
    rw [hid]
    exact S04V.add_lt_one A
      (S04V.sub_lt_one A hr₃ (S04V.mul_lt_one_of_le_of_lt A (S04V.le_one A h₃) hsum)) hprod
  have h₃₂ : A.valuation (t₃ - t₂) = 1 := by rw [Valuation.map_sub_swap]; exact h₂₃
  have := S04V.lt_one_of_mul_lt_one_of_eq_one A hkey h₃₂
  rwa [Valuation.map_sub_swap] at this

section Frame

local notation "Qb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ)

@[scoped simp] lemma frame_a₁ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.a₁ = (W.a₁ : Qb) := by simp
@[scoped simp] lemma frame_a₂ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.a₂ = (W.a₂ : Qb) := by simp
@[scoped simp] lemma frame_a₃ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.a₃ = (W.a₃ : Qb) := by simp
@[scoped simp] lemma frame_a₄ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.a₄ = (W.a₄ : Qb) := by simp
@[scoped simp] lemma frame_a₆ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.a₆ = (W.a₆ : Qb) := by simp

lemma frame_negY (x y : Qb) :
    ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x y = -y - (W.a₁ : Qb) * x - W.a₃ := by
  simp [negY]

lemma frame_eqn {x y : Qb} (h : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x y) :
    y ^ 2 + (W.a₁ : Qb) * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  have := (equation_iff x y).mp h.left
  simpa using this

lemma frame_shifted_eqn {x₀ y₀ : Qb}
    (hFy : 2 * y₀ + (W.a₁ : Qb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : Qb} (h : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x y) :
    (y - y₀) ^ 2 + (W.a₁ : Qb) * (x - x₀) * (y - y₀) =
      (x - x₀) ^ 3 + ((W.a₂ : Qb) + 3 * x₀) * (x - x₀) ^ 2
        - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  linear_combination frame_eqn W h - (x - x₀) * hFx - (y - y₀) * hFy

variable (A : ValuationSubring Qb)

lemma frame_intCast_le (n : ℤ) : A.valuation (n : Qb) ≤ 1 := S04V.intCast_le A n

theorem S04_n_slope
    {x₀ y₀ : Qb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Qb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : Qb}
    (h : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    (y - y₀) / (x - x₀) ∈ A ∧ A.valuation (y - y₀) < 1 ∧
      A.valuation (((y - y₀) / (x - x₀)) ^ 2 + (W.a₁ : Qb) * ((y - y₀) / (x - x₀))
        - ((W.a₂ : Qb) + 3 * x₀)) < 1 := by
  have _ := hy₀
  set F₀ := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    with hF₀
  set X := x - x₀ with hXdef
  set Y := y - y₀ with hYdef
  set t := Y / X with ht
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh
  have hvX0 : 0 < A.valuation X := (Valuation.pos_iff _).mpr hX0
  have heq := frame_shifted_eqn W hFy hFx h
  rw [← hF₀] at heq

  have ht_id : t ^ 2 + (W.a₁ : Qb) * t - ((W.a₂ : Qb) + 3 * x₀) = X - F₀ / X ^ 2 := by
    rw [ht]
    field_simp
    linear_combination heq
  have hsmall : A.valuation (X - F₀ / X ^ 2) < 1 := by
    refine S04V.sub_lt_one A hX ?_
    rw [Valuation.map_div, Valuation.map_pow]
    exact (div_lt_one₀ (pow_pos hvX0 2)).mpr hsh
  have ha₁ : A.valuation (W.a₁ : Qb) ≤ 1 := frame_intCast_le A _
  have ha₂' : A.valuation ((W.a₂ : Qb) + 3 * x₀) ≤ 1 :=
    S04V.add_le_one A (frame_intCast_le A _)
      (S04V.v_mul_le_one A (S04V.ofNat_le A 3) (S04V.le_one A hx₀))

  have htA : A.valuation t ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have ht0 : 0 < A.valuation t := lt_trans zero_lt_one hgt
    have h2 : A.valuation t < A.valuation (t ^ 2) := by
      rw [Valuation.map_pow, pow_two]
      have := mul_lt_mul_of_pos_right hgt ht0
      rwa [one_mul] at this
    have hgt2 : 1 < A.valuation (t ^ 2) := lt_trans hgt h2
    have hs1 : A.valuation (t ^ 2 + (W.a₁ : Qb) * t) = A.valuation (t ^ 2) := by
      apply S04V.add_eq_left A
      calc A.valuation ((W.a₁ : Qb) * t) = A.valuation (W.a₁ : Qb) * A.valuation t :=
            Valuation.map_mul _ _ _
        _ ≤ 1 * A.valuation t := mul_le_mul' ha₁ le_rfl
        _ = A.valuation t := one_mul _
        _ < A.valuation (t ^ 2) := h2
    have hs2 : A.valuation (t ^ 2 + (W.a₁ : Qb) * t - ((W.a₂ : Qb) + 3 * x₀)) =
        A.valuation (t ^ 2) := by
      rw [S04V.sub_eq_left A (by rw [hs1]; exact lt_of_le_of_lt ha₂' hgt2), hs1]
    have hzero : t ^ 2 + (W.a₁ : Qb) * t - ((W.a₂ : Qb) + 3 * x₀) - (X - F₀ / X ^ 2) = 0 := by
      rw [ht_id, sub_self]
    have hs3 : A.valuation (t ^ 2 + (W.a₁ : Qb) * t - ((W.a₂ : Qb) + 3 * x₀) - (X - F₀ / X ^ 2)) =
        A.valuation (t ^ 2) := by
      rw [S04V.sub_eq_left A (by rw [hs2]; exact lt_trans hsmall hgt2), hs2]
    rw [hzero, Valuation.map_zero] at hs3
    rw [← hs3] at hgt2
    exact not_lt_zero hgt2
  refine ⟨S04V.mem A htA, ?_, by rw [ht_id]; exact hsmall⟩

  have hY : Y = t * X := by rw [ht, div_mul_cancel₀ _ hX0]
  rw [hY, Valuation.map_mul]
  calc A.valuation t * A.valuation X ≤ 1 * A.valuation X := mul_le_mul' htA le_rfl
    _ = A.valuation X := one_mul _
    _ < 1 := hX

theorem S04_n_neg
    {x₀ y₀ : Qb} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : Qb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : Qb) + 12 * x₀) = 1)
    {x y : Qb}
    (h : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    A.valuation ((y - y₀) / (x - x₀)
      - (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x y - y₀) / (x - x₀)) = 1 := by
  obtain ⟨htA, -, hroot⟩ := S04_n_slope W A hx₀ hy₀ hFy hFx h hX hsh
  set t := (y - y₀) / (x - x₀) with ht
  have hX0 : x - x₀ ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero, zero_pow two_ne_zero] at hsh
    exact not_lt_zero hsh

  have hdiff : t - (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x y - y₀) / (x - x₀) =
      2 * t + (W.a₁ : Qb) := by
    rw [frame_negY, ht]
    field_simp
    linear_combination hFy
  rw [hdiff]

  have hsq : (2 * t + (W.a₁ : Qb)) ^ 2 =
      4 * (t ^ 2 + (W.a₁ : Qb) * t - ((W.a₂ : Qb) + 3 * x₀)) + ((W.b₂ : Qb) + 12 * x₀) := by
    simp only [WeierstrassCurve.b₂]; push_cast; ring
  have hunit : A.valuation ((2 * t + (W.a₁ : Qb)) ^ 2) = 1 := by
    rw [hsq]
    exact S04V.small_add_unit A (S04V.mul_lt_one_of_le_of_lt A (S04V.ofNat_le A 4) hroot) hnode
  rw [Valuation.map_pow] at hunit
  exact S04V.eq_one_of_pow_eq_one A two_ne_zero hunit

end Frame

section IdentCore

variable {K : Type*} [Field K]

theorem S04_dbl_core (x y x₀ y₀ a₁ a₂ a₆ : K)
    (heqn : y ^ 2 + a₁ * x * y + (-2 * y₀ - a₁ * x₀) * y =
      x ^ 3 + a₂ * x ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x + a₆) :
    (3 * x ^ 2 + 2 * a₂ * x + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) - a₁ * y) ^ 2
      + a₁ * (3 * x ^ 2 + 2 * a₂ * x + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) - a₁ * y)
          * (2 * y + a₁ * x + (-2 * y₀ - a₁ * x₀))
      - (a₂ + 2 * x + x₀) * (2 * y + a₁ * x + (-2 * y₀ - a₁ * x₀)) ^ 2
    = (x - x₀) ^ 4
      + 8 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
          - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)) * (x - x₀)
      + (a₁ ^ 2 + 4 * a₂ + 12 * x₀)
        * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
          - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)) := by
  linear_combination (-(a₁ ^ 2 + 4 * a₂ + 12 * x₀) - 8 * (x - x₀)) * heqn

theorem S04_pm_core (x₁ y₁ x₂ y₂ x₀ y₀ a₁ a₂ a₆ : K)
    (heqn₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + (-2 * y₀ - a₁ * x₀) * y₁ =
      x₁ ^ 3 + a₂ * x₁ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₁ + a₆)
    (heqn₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + (-2 * y₀ - a₁ * x₀) * y₂ =
      x₂ ^ 3 + a₂ * x₂ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₂ + a₆) :
    (4 * ((y₁ - y₂) ^ 2 + a₁ * (y₁ - y₂) * (x₁ - x₂) - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2))
      * (4 * ((y₁ + y₂ + a₁ * x₂ + (-2 * y₀ - a₁ * x₀)) ^ 2
          + a₁ * (y₁ + y₂ + a₁ * x₂ + (-2 * y₀ - a₁ * x₀)) * (x₁ - x₂)
          - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2))
    = 16 * (((x₁ - x₀) * (x₂ - x₀)) ^ 2
        + (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
            - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆))
          * (4 * (x₁ - x₀) + 4 * (x₂ - x₀) + (a₁ ^ 2 + 4 * a₂ + 12 * x₀))) * (x₁ - x₂) ^ 2 := by
  linear_combination
    (4 * (((2 * (y₁ - y₀) + a₁ * (x₁ - x₀)) ^ 2 - (2 * (y₂ - y₀) + a₁ * (x₂ - x₀)) ^ 2
        + (4 * (x₁ - x₀) ^ 3 + (a₁ ^ 2 + 4 * a₂ + 12 * x₀) * (x₁ - x₀) ^ 2
            - 4 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
              - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)))
        - (4 * (x₂ - x₀) ^ 3 + (a₁ ^ 2 + 4 * a₂ + 12 * x₀) * (x₂ - x₀) ^ 2
            - 4 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
              - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆))))
        - 2 * ((a₁ ^ 2 + 4 * a₂ + 12 * x₀) + 4 * (x₁ - x₀) + 4 * (x₂ - x₀)) * (x₁ - x₂) ^ 2))
      * heqn₁
    + (4 * (-(((2 * (y₁ - y₀) + a₁ * (x₁ - x₀)) ^ 2 - (2 * (y₂ - y₀) + a₁ * (x₂ - x₀)) ^ 2
        + (4 * (x₁ - x₀) ^ 3 + (a₁ ^ 2 + 4 * a₂ + 12 * x₀) * (x₁ - x₀) ^ 2
            - 4 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
              - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)))
        - (4 * (x₂ - x₀) ^ 3 + (a₁ ^ 2 + 4 * a₂ + 12 * x₀) * (x₂ - x₀) ^ 2
            - 4 * (y₀ ^ 2 + a₁ * x₀ * y₀ + (-2 * y₀ - a₁ * x₀) * y₀
              - (x₀ ^ 3 + a₂ * x₀ ^ 2 + (a₁ * y₀ - 3 * x₀ ^ 2 - 2 * a₂ * x₀) * x₀ + a₆)))))
        - 2 * ((a₁ ^ 2 + 4 * a₂ + 12 * x₀) + 4 * (x₁ - x₀) + 4 * (x₂ - x₀)) * (x₁ - x₂) ^ 2))
      * heqn₂

end IdentCore

section IdentFrame

local notation "Qb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ)

theorem S04_dbl_ident {x₀ y₀ : Qb}
    (hFy : 2 * y₀ + (W.a₁ : Qb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : Qb} (h : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x y)
    (hΨ : 2 * y + (W.a₁ : Qb) * x + W.a₃ ≠ 0) :
    (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.addX x x
        (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.slope x x y y) - x₀)
      * (2 * y + (W.a₁ : Qb) * x + W.a₃) ^ 2 =
    (x - x₀) ^ 4
      + 8 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          * (x - x₀)
      + ((W.b₂ : Qb) + 12 * x₀)
          * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  have ha₃ : (W.a₃ : Qb) = -2 * y₀ - (W.a₁ : Qb) * x₀ := by linear_combination hFy
  have ha₄ : (W.a₄ : Qb) = (W.a₁ : Qb) * y₀ - 3 * x₀ ^ 2 - 2 * (W.a₂ : Qb) * x₀ := by
    linear_combination -hFx
  have heqn := frame_eqn W h
  have hy : y ≠ ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x y := by
    rw [frame_negY]; intro hyy; apply hΨ; linear_combination hyy
  have hden : y - ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x y =
      2 * y + (W.a₁ : Qb) * x + W.a₃ := by
    rw [frame_negY]; ring
  rw [slope_of_Y_ne rfl hy, hden]
  simp only [addX, frame_a₁, frame_a₂, frame_a₄, WeierstrassCurve.b₂]
  push_cast
  rw [ha₃] at hΨ
  rw [ha₃, ha₄] at heqn ⊢
  set N := 3 * x ^ 2 + 2 * (W.a₂ : Qb) * x + ((W.a₁ : Qb) * y₀ - 3 * x₀ ^ 2 - 2 * (W.a₂ : Qb) * x₀)
    - (W.a₁ : Qb) * y with hN
  set D := 2 * y + (W.a₁ : Qb) * x + (-2 * y₀ - (W.a₁ : Qb) * x₀) with hD
  have hND : N / D * D = N := div_mul_cancel₀ N hΨ
  have key : ((N / D) ^ 2 + (W.a₁ : Qb) * (N / D) - (W.a₂ : Qb) - x - x - x₀) * D ^ 2
      = N ^ 2 + (W.a₁ : Qb) * N * D - ((W.a₂ : Qb) + 2 * x + x₀) * D ^ 2 := by
    have e : ((N / D) ^ 2 + (W.a₁ : Qb) * (N / D) - (W.a₂ : Qb) - x - x - x₀) * D ^ 2
        = (N / D * D) ^ 2 + (W.a₁ : Qb) * (N / D * D) * D - ((W.a₂ : Qb) + 2 * x + x₀) * D ^ 2 := by
      ring
    rw [e, hND]
  rw [key, hN, hD]
  linear_combination S04_dbl_core x y x₀ y₀ (W.a₁ : Qb) (W.a₂ : Qb) (W.a₆ : Qb) heqn

theorem S04_pm_ident {x₀ y₀ : Qb}
    (hFy : 2 * y₀ + (W.a₁ : Qb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Qb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x₁ y₁ x₂ y₂ : Qb}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.addX x₁ x₂
        (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.slope x₁ x₂ y₁ y₂) - x₀)
      * (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.addX x₁ x₂
          (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.slope x₁ x₂ y₁
            (((W.map (Int.castRingHom ℚ))⁄Qb).toAffine.negY x₂ y₂)) - x₀)
      * (x₁ - x₂) ^ 2 =
    ((x₁ - x₀) * (x₂ - x₀)) ^ 2
      + (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          * (4 * (x₁ - x₀) + 4 * (x₂ - x₀) + ((W.b₂ : Qb) + 12 * x₀)) := by
  have ha₃ : (W.a₃ : Qb) = -2 * y₀ - (W.a₁ : Qb) * x₀ := by linear_combination hFy
  have ha₄ : (W.a₄ : Qb) = (W.a₁ : Qb) * y₀ - 3 * x₀ ^ 2 - 2 * (W.a₂ : Qb) * x₀ := by
    linear_combination -hFx
  have heqn₁ := frame_eqn W h₁
  have heqn₂ := frame_eqn W h₂
  have hδ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, slope_of_X_ne hx]
  simp only [addX, frame_a₁, frame_a₂, frame_negY, WeierstrassCurve.b₂]
  push_cast
  rw [ha₃, ha₄] at heqn₁ heqn₂ ⊢
  set a₁ := (W.a₁ : Qb) with ha₁
  set a₂ := (W.a₂ : Qb) with ha₂
  set a₆ := (W.a₆ : Qb) with ha₆
  set μ := (y₁ - y₂) / (x₁ - x₂) with hμ
  set ν := (y₁ - (-y₂ - a₁ * x₂ - (-2 * y₀ - a₁ * x₀))) / (x₁ - x₂) with hν
  have hμδ : μ * (x₁ - x₂) = y₁ - y₂ := div_mul_cancel₀ _ hδ
  have hνδ : ν * (x₁ - x₂) = y₁ - (-y₂ - a₁ * x₂ - (-2 * y₀ - a₁ * x₀)) := div_mul_cancel₀ _ hδ
  have eU : (μ ^ 2 + a₁ * μ - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2) =
      4 * ((y₁ - y₂) ^ 2 + a₁ * (y₁ - y₂) * (x₁ - x₂) - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2) := by
    have e : (μ ^ 2 + a₁ * μ - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2) =
        4 * ((μ * (x₁ - x₂)) ^ 2 + a₁ * (μ * (x₁ - x₂)) * (x₁ - x₂)
          - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2) := by ring
    rw [e, hμδ]
  have eV : (ν ^ 2 + a₁ * ν - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2) =
      4 * ((y₁ + y₂ + a₁ * x₂ + (-2 * y₀ - a₁ * x₀)) ^ 2
          + a₁ * (y₁ + y₂ + a₁ * x₂ + (-2 * y₀ - a₁ * x₀)) * (x₁ - x₂)
          - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2) := by
    have e : (ν ^ 2 + a₁ * ν - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2) =
        4 * ((ν * (x₁ - x₂)) ^ 2 + a₁ * (ν * (x₁ - x₂)) * (x₁ - x₂)
          - (a₂ + x₁ + x₂ + x₀) * (x₁ - x₂) ^ 2) := by ring
    rw [e, hνδ]; ring
  have h16 : (16 : Qb) * (x₁ - x₂) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hδ)
  apply mul_right_cancel₀ h16
  have core := S04_pm_core x₁ y₁ x₂ y₂ x₀ y₀ a₁ a₂ a₆ heqn₁ heqn₂
  calc (μ ^ 2 + a₁ * μ - a₂ - x₁ - x₂ - x₀) * (ν ^ 2 + a₁ * ν - a₂ - x₁ - x₂ - x₀) * (x₁ - x₂) ^ 2
        * (16 * (x₁ - x₂) ^ 2)
      = ((μ ^ 2 + a₁ * μ - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2))
        * ((ν ^ 2 + a₁ * ν - a₂ - x₁ - x₂ - x₀) * (4 * (x₁ - x₂) ^ 2)) := by ring
    _ = _ := by rw [eU, eV, core]; ring

end IdentFrame

end

theorem solution
    (W : WeierstrassCurve ℤ) {x₀ y₀ : AlgebraicClosure ℚ}
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hΨ : 2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + W.a₃ ≠ 0) :
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.addX x x
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.slope x x y y) - x₀)
      * (2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + W.a₃) ^ 2 =
    (x - x₀) ^ 4
      + 8 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          * (x - x₀)
      + ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀)
          * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) :=
  S04_dbl_ident W hFy hFx h hΨ

end S_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre
end P2MW
export P2MW.S_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre (solution)
