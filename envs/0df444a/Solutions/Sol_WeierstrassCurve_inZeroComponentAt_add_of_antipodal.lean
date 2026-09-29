-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_add_of_antipodal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6b1ae8bc-4b2e-5c80-8499-59fe781e27ea

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_node_chord_trichotomy
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_of_valuation_sub_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_add_of_antipodal

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace TFDispAnti

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "L" => AlgebraicClosure ℚ
local notation "v" => ValuationSubring.valuation A
local notation "E" => ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))

theorem E_a₁ : (E).toAffine.a₁ = (W.a₁ : L) := by simp
theorem E_a₂ : (E).toAffine.a₂ = (W.a₂ : L) := by simp
theorem E_a₃ : (E).toAffine.a₃ = (W.a₃ : L) := by simp
theorem E_a₄ : (E).toAffine.a₄ = (W.a₄ : L) := by simp
theorem E_a₆ : (E).toAffine.a₆ = (W.a₆ : L) := by simp

theorem E_equation_iff (x y : L) : (E).toAffine.Equation x y ↔
    y ^ 2 + (W.a₁ : L) * x * y + (W.a₃ : L) * y
      = x ^ 3 + (W.a₂ : L) * x ^ 2 + (W.a₄ : L) * x + (W.a₆ : L) := by
  rw [equation_iff, E_a₁, E_a₂, E_a₃, E_a₄, E_a₆]

theorem E_negY (x y : L) : (E).toAffine.negY x y = -y - (W.a₁ : L) * x - (W.a₃ : L) := by
  rw [negY, E_a₁, E_a₃]

theorem E_addX (x₁ x₂ ℓ : L) :
    (E).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 + (W.a₁ : L) * ℓ - (W.a₂ : L) - x₁ - x₂ := by
  rw [addX, E_a₁, E_a₂]

variable {W A}

theorem one_lt_val_of_notMem {x : L} (hx : x ∉ A) : 1 < v x :=
  not_le.mp fun h => hx ((A.valuation_le_one_iff x).mp h)

theorem mem_of_val_le_one {x : L} (hx : v x ≤ 1) : x ∈ A := (A.valuation_le_one_iff x).mp hx

theorem val_le_one_of_mem {x : L} (hx : x ∈ A) : v x ≤ 1 := (A.valuation_le_one_iff x).mpr hx

theorem val_intCast_le_one (n : ℤ) : v (n : L) ≤ 1 := val_le_one_of_mem (intCast_mem A n)

theorem mem_of_quadratic_root {a b z : L} (ha : a ∈ A) (hb : b ∈ A)
    (hz : z ^ 2 + a * z - b = 0) : z ∈ A := by
  by_contra hzA
  have hz1 : 1 < v z := one_lt_val_of_notMem hzA
  have hz0 : v z ≠ 0 := (zero_lt_one.trans hz1).ne'
  have hsq : v (a * z - b) < v (z ^ 2) := by
    rw [Valuation.map_pow]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      calc v a * v z ≤ 1 * v z := mul_le_mul' (val_le_one_of_mem ha) le_rfl
        _ = v z := one_mul _
        _ < v z ^ 2 := by rw [sq]; exact lt_mul_self hz1
    · calc v b ≤ 1 := val_le_one_of_mem hb
        _ < v z ^ 2 := by rw [sq]; exact one_lt_mul'' hz1 hz1
  have : v (z ^ 2 + (a * z - b)) = v (z ^ 2) := Valuation.map_add_eq_of_lt_left _ hsq
  rw [show z ^ 2 + (a * z - b) = z ^ 2 + a * z - b by ring, hz, Valuation.map_zero,
    Valuation.map_pow] at this
  exact hz0 (pow_eq_zero_iff two_ne_zero |>.mp this.symm)

theorem eq_of_sq_eq_sq {a b : A.ValueGroup} (h : a * a = b * b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (mul_lt_mul'' hab hab zero_le' zero_le'))
  · exact hab
  · exact absurd h (ne_of_gt (mul_lt_mul'' hab hab zero_le' zero_le'))

section Frame

variable {x₀ y₀ α β : L}

theorem toric_eq
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : L} (h : (E).toAffine.Equation x y) :
    ((y - y₀) - α * (x - x₀)) * ((y - y₀) - β * (x - x₀))
      = (x - x₀) ^ 3 - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  rw [E_equation_iff] at h
  linear_combination h - (x - x₀) * hFx - (y - y₀) * hFy - (x - x₀) * (y - y₀) * hsum
    + (x - x₀) ^ 2 * hprod

theorem neg_s (hsum : α + β = -(W.a₁ : L)) (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (x y : L) :
    ((E).toAffine.negY x y - y₀) - α * (x - x₀) = -((y - y₀) - β * (x - x₀)) := by
  rw [E_negY]
  linear_combination (-(x - x₀)) * hsum - hFy

theorem sub_mul_X (x y : L) :
    (β - α) * (x - x₀) = ((y - y₀) - α * (x - x₀)) - ((y - y₀) - β * (x - x₀)) := by ring

theorem val_X_le (hαβ : v (α - β) = 1) {x y : L} {m : A.ValueGroup}
    (hs : v ((y - y₀) - α * (x - x₀)) ≤ m) (ht : v ((y - y₀) - β * (x - x₀)) ≤ m) :
    v (x - x₀) ≤ m := by
  have hβα : v (β - α) = 1 := by rw [Valuation.map_sub_swap, hαβ]
  have key : v (x - x₀) = v (((y - y₀) - α * (x - x₀)) - ((y - y₀) - β * (x - x₀))) := by
    rw [← sub_mul_X, Valuation.map_mul, hβα, one_mul]
  rw [key]
  exact Valuation.map_sub_le _ hs ht

theorem val_X_eq (hαβ : v (α - β) = 1) (x y : L) :
    v (x - x₀) = v (((y - y₀) - α * (x - x₀)) - ((y - y₀) - β * (x - x₀))) := by
  have hβα : v (β - α) = 1 := by rw [Valuation.map_sub_swap, hαβ]
  rw [← sub_mul_X, Valuation.map_mul, hβα, one_mul]

theorem y_mem_of_x_mem {x y : L} (h : (E).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  rw [E_equation_iff] at h
  apply mem_of_quadratic_root (a := (W.a₁ : L) * x + W.a₃)
    (b := x ^ 3 + (W.a₂ : L) * x ^ 2 + (W.a₄ : L) * x + (W.a₆ : L))
  · exact add_mem (mul_mem (intCast_mem A _) hx) (intCast_mem A _)
  · exact add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem (intCast_mem A _) (pow_mem hx 2))) (mul_mem (intCast_mem A _) hx))
      (intCast_mem A _)
  · linear_combination h

theorem val_Y_lt_one (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A) (hα : α ∈ A) (hβ : β ∈ A)
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hbad : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x y : L} (h : (E).toAffine.Equation x y) (hX : v (x - x₀) < 1) :
    v (y - y₀) < 1 := by
  have hxA : x ∈ A := by
    have : x = (x - x₀) + x₀ := by ring
    rw [this]; exact add_mem (mem_of_val_le_one hX.le) hx₀
  have hyA : y ∈ A := y_mem_of_x_mem h hxA
  have hY : v (y - y₀) ≤ 1 := val_le_one_of_mem (sub_mem hyA hy₀)
  have hXA : v (x - x₀) ≤ 1 := hX.le

  have hst : v (((y - y₀) - α * (x - x₀)) * ((y - y₀) - β * (x - x₀))) < 1 := by
    rw [toric_eq hsum hprod hFy hFx h]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hbad)
    rw [Valuation.map_pow]
    calc v (x - x₀) ^ 3 ≤ v (x - x₀) ^ 1 := pow_le_pow_right_of_le_one' hXA (by norm_num)
      _ < 1 := by rw [pow_one]; exact hX
  rw [Valuation.map_mul] at hst
  have hs1 : v ((y - y₀) - α * (x - x₀)) ≤ 1 :=
    Valuation.map_sub_le _ hY (by rw [Valuation.map_mul]; exact mul_le_one' (val_le_one_of_mem hα) hXA)
  have ht1 : v ((y - y₀) - β * (x - x₀)) ≤ 1 :=
    Valuation.map_sub_le _ hY (by rw [Valuation.map_mul]; exact mul_le_one' (val_le_one_of_mem hβ) hXA)

  have key : v ((y - y₀) - α * (x - x₀)) < 1 ∨ v ((y - y₀) - β * (x - x₀)) < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : v ((y - y₀) - α * (x - x₀)) = 1 := le_antisymm hs1 hcon.1
    have h2 : v ((y - y₀) - β * (x - x₀)) = 1 := le_antisymm ht1 hcon.2
    rw [h1, h2, one_mul] at hst
    exact lt_irrefl _ hst
  rcases key with hs | ht
  · have : y - y₀ = ((y - y₀) - α * (x - x₀)) + α * (x - x₀) := by ring
    rw [this]
    refine Valuation.map_add_lt _ hs ?_
    rw [Valuation.map_mul]
    calc v α * v (x - x₀) ≤ 1 * v (x - x₀) := mul_le_mul' (val_le_one_of_mem hα) le_rfl
      _ < 1 := by rw [one_mul]; exact hX
  · have : y - y₀ = ((y - y₀) - β * (x - x₀)) + β * (x - x₀) := by ring
    rw [this]
    refine Valuation.map_add_lt _ ht ?_
    rw [Valuation.map_mul]
    calc v β * v (x - x₀) ≤ 1 * v (x - x₀) := mul_le_mul' (val_le_one_of_mem hβ) le_rfl
      _ < 1 := by rw [one_mul]; exact hX

theorem val_s_eq_val_t_of_antipodal (hαβ : v (α - β) = 1)
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : L} (h : (E).toAffine.Equation x y) (hX : v (x - x₀) < 1)
    (hanti : v (x - x₀) ^ 2 ≤ v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) :
    v ((y - y₀) - α * (x - x₀)) = v ((y - y₀) - β * (x - x₀)) := by
  set s := (y - y₀) - α * (x - x₀) with hs_def
  set t := (y - y₀) - β * (x - x₀) with ht_def
  set F₀ := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hF₀_def
  by_contra hne

  have hXst : v (x - x₀) = max (v s) (v t) := by
    have hne' : v s ≠ v (-t) := by rwa [Valuation.map_neg]
    rw [val_X_eq hαβ x y, ← hs_def, ← ht_def, sub_eq_add_neg,
      Valuation.map_add_of_distinct_val _ hne', Valuation.map_neg]
  have hst : s * t = (x - x₀) ^ 3 - F₀ := toric_eq hsum hprod hFy hFx h

  have hlt : v (s * t) < v (x - x₀) ^ 2 := by
    rw [Valuation.map_mul, sq, hXst]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [max_eq_right hlt.le]
      exact mul_lt_mul_of_pos_right hlt (lt_of_le_of_lt zero_le' hlt)
    · rw [max_eq_left hlt.le]
      exact mul_lt_mul_of_pos_left hlt (lt_of_le_of_lt zero_le' hlt)

  have hX3 : v ((x - x₀) ^ 3) < v (x - x₀) ^ 2 := by
    rw [Valuation.map_pow, pow_succ, sq]
    have h0 : v (x - x₀) ≠ 0 := by
      intro h0
      rw [h0] at hXst

      rw [h0, sq, mul_zero] at hlt
      exact (not_lt_of_ge zero_le') hlt
    calc v (x - x₀) * v (x - x₀) * v (x - x₀)
        < v (x - x₀) * v (x - x₀) * 1 := by
          exact mul_lt_mul_of_pos_left hX (lt_of_le_of_ne zero_le'
            (Ne.symm (mul_ne_zero h0 h0)))
      _ = v (x - x₀) * v (x - x₀) := mul_one _
  have hF : v F₀ = v ((x - x₀) ^ 3 - s * t) := by
    congr 1; rw [hst]; ring
  have : v ((x - x₀) ^ 3 - s * t) < v (x - x₀) ^ 2 :=
    lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hX3 hlt)
  rw [← hF] at this
  exact (not_lt_of_ge hanti) this

theorem val_s_lt_one (hα : α ∈ A) {x y : L} (hX : v (x - x₀) < 1) (hY : v (y - y₀) < 1) :
    v ((y - y₀) - α * (x - x₀)) < 1 := by
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hY ?_)
  rw [Valuation.map_mul]
  calc v α * v (x - x₀) ≤ 1 * v (x - x₀) := mul_le_mul' (val_le_one_of_mem hα) le_rfl
    _ < 1 := by rw [one_mul]; exact hX

theorem sq_eq_of_middle (hα : α ∈ A) (hαβ : v (α - β) = 1)
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : L} (h : (E).toAffine.Equation x y) (hX : v (x - x₀) < 1) (hY : v (y - y₀) < 1)
    (hm : v ((y - y₀) - α * (x - x₀)) = v ((y - y₀) - β * (x - x₀))) :
    v ((y - y₀) - α * (x - x₀)) * v ((y - y₀) - α * (x - x₀))
      = v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  set s := (y - y₀) - α * (x - x₀) with hs_def
  set t := (y - y₀) - β * (x - x₀) with ht_def
  set F₀ := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hF₀_def
  set m := v s with hm_def
  have hm1 : m < 1 := val_s_lt_one hα hX hY
  have hXm : v (x - x₀) ≤ m := val_X_le hαβ le_rfl hm.symm.le
  have hst : s * t = (x - x₀) ^ 3 - F₀ := toric_eq hsum hprod hFy hFx h
  have hvst : v (s * t) = m * m := by rw [Valuation.map_mul, ← hm]
  have hF : F₀ = (x - x₀) ^ 3 - s * t := by rw [hst]; ring
  by_cases hm0 : m = 0
  ·
    have hs0 : s = 0 := (Valuation.zero_iff _).mp hm0
    have ht0 : t = 0 := (Valuation.zero_iff _).mp (hm ▸ hm0)
    have hβα : β - α ≠ 0 := by
      intro h0
      have : v (α - β) = 0 := by rw [Valuation.map_sub_swap, h0, Valuation.map_zero]
      rw [hαβ] at this; exact one_ne_zero this
    have hX0 : x - x₀ = 0 := by
      have key := sub_mul_X (α := α) (β := β) (x₀ := x₀) (y₀ := y₀) x y
      rw [← hs_def, ← ht_def, hs0, ht0, sub_zero] at key
      exact (mul_eq_zero.mp key).resolve_left hβα
    rw [hm0, zero_mul, hF, hX0, hs0, zero_mul, sub_zero, zero_pow three_ne_zero, Valuation.map_zero]
  · have hm_pos : 0 < m := lt_of_le_of_ne zero_le' (Ne.symm hm0)

    have hX3 : v ((x - x₀) ^ 3) < v (s * t) := by
      rw [hvst, Valuation.map_pow]
      calc v (x - x₀) ^ 3 ≤ m ^ 3 := pow_le_pow_left' hXm 3
        _ = m * m * m := by rw [pow_succ, sq]
        _ < m * m * 1 := mul_lt_mul_of_pos_left hm1 (mul_pos hm_pos hm_pos)
        _ = m * m := mul_one _
    rw [hF, Valuation.map_sub_eq_of_lt_right _ hX3, hvst]

theorem val_ds_eq_val_dt_of_middle (hαβ : v (α - β) = 1)
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x₁ y₁ x₂ y₂ : L} (h₁ : (E).toAffine.Equation x₁ y₁) (h₂ : (E).toAffine.Equation x₂ y₂)
    {m : A.ValueGroup} (hm1 : m < 1)
    (hs₁ : v ((y₁ - y₀) - α * (x₁ - x₀)) = m) (ht₁ : v ((y₁ - y₀) - β * (x₁ - x₀)) = m)
    (hs₂ : v ((y₂ - y₀) - α * (x₂ - x₀)) = m) (ht₂ : v ((y₂ - y₀) - β * (x₂ - x₀)) = m) :
    v ((y₁ - y₂) - α * (x₁ - x₂)) = v ((y₁ - y₂) - β * (x₁ - x₂)) := by
  set s₁ := (y₁ - y₀) - α * (x₁ - x₀) with hs₁_def
  set t₁ := (y₁ - y₀) - β * (x₁ - x₀) with ht₁_def
  set s₂ := (y₂ - y₀) - α * (x₂ - x₀) with hs₂_def
  set t₂ := (y₂ - y₀) - β * (x₂ - x₀) with ht₂_def
  set F₀ := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hF₀_def
  have hds : (y₁ - y₂) - α * (x₁ - x₂) = s₁ - s₂ := by ring
  have hdt : (y₁ - y₂) - β * (x₁ - x₂) = t₁ - t₂ := by ring
  rw [hds, hdt]
  by_cases hm0 : m = 0
  ·
    have e₁ : s₁ = 0 := (Valuation.zero_iff _).mp (hs₁.trans hm0)
    have e₂ : s₂ = 0 := (Valuation.zero_iff _).mp (hs₂.trans hm0)
    have e₃ : t₁ = 0 := (Valuation.zero_iff _).mp (ht₁.trans hm0)
    have e₄ : t₂ = 0 := (Valuation.zero_iff _).mp (ht₂.trans hm0)
    rw [e₁, e₂, e₃, e₄]
  have hm_pos : 0 < m := lt_of_le_of_ne zero_le' (Ne.symm hm0)

  have hst₁ : s₁ * t₁ = (x₁ - x₀) ^ 3 - F₀ := toric_eq hsum hprod hFy hFx h₁
  have hst₂ : s₂ * t₂ = (x₂ - x₀) ^ 3 - F₀ := toric_eq hsum hprod hFy hFx h₂
  have key : t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)
      = (x₁ - x₂) * ((x₁ - x₀) ^ 2 + (x₁ - x₀) * (x₂ - x₀) + (x₂ - x₀) ^ 2) := by
    linear_combination hst₁ - hst₂

  have hX₁ : v (x₁ - x₀) ≤ m := val_X_le hαβ hs₁.le ht₁.le
  have hX₂ : v (x₂ - x₀) ≤ m := val_X_le hαβ hs₂.le ht₂.le
  have hQ : v ((x₁ - x₀) ^ 2 + (x₁ - x₀) * (x₂ - x₀) + (x₂ - x₀) ^ 2) ≤ m * m := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · rw [Valuation.map_pow, sq]; exact mul_le_mul' hX₁ hX₁
    · rw [Valuation.map_mul]; exact mul_le_mul' hX₁ hX₂
    · rw [Valuation.map_pow, sq]; exact mul_le_mul' hX₂ hX₂
  have hdx : (β - α) * (x₁ - x₂) = (s₁ - s₂) - (t₁ - t₂) := by ring
  have hβα : v (β - α) = 1 := by rw [Valuation.map_sub_swap, hαβ]
  have hvdx : v (x₁ - x₂) = v ((s₁ - s₂) - (t₁ - t₂)) := by
    rw [← hdx, Valuation.map_mul, hβα, one_mul]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    have hvdx' : v (x₁ - x₂) = v (t₁ - t₂) := by
      rw [hvdx, Valuation.map_sub_eq_of_lt_right _ hlt]
    have hpos : 0 < v (t₁ - t₂) := lt_of_le_of_lt zero_le' hlt
    have hL : v (t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)) = m * v (t₁ - t₂) := by
      rw [Valuation.map_add_eq_of_lt_right, Valuation.map_mul, hs₁]
      rw [Valuation.map_mul, Valuation.map_mul, ht₂, hs₁]
      exact mul_lt_mul_of_pos_left hlt hm_pos
    have hR : v ((x₁ - x₂) * ((x₁ - x₀) ^ 2 + (x₁ - x₀) * (x₂ - x₀) + (x₂ - x₀) ^ 2))
        ≤ v (t₁ - t₂) * (m * m) := by
      rw [Valuation.map_mul, hvdx']; exact mul_le_mul' le_rfl hQ
    rw [← key, hL] at hR

    have : m * v (t₁ - t₂) ≤ (m * m) * v (t₁ - t₂) := by rwa [mul_comm (v (t₁ - t₂))] at hR
    have h1 : m * 1 ≤ m * m := by
      rw [mul_one]; exact le_of_mul_le_mul_right this hpos
    exact (not_le_of_gt hm1) (le_of_mul_le_mul_left h1 hm_pos)
  ·
    have hvdx' : v (x₁ - x₂) = v (s₁ - s₂) := by
      rw [hvdx, Valuation.map_sub_eq_of_lt_left _ hlt]
    have hpos : 0 < v (s₁ - s₂) := lt_of_le_of_lt zero_le' hlt
    have hL : v (t₂ * (s₁ - s₂) + s₁ * (t₁ - t₂)) = m * v (s₁ - s₂) := by
      rw [Valuation.map_add_eq_of_lt_left, Valuation.map_mul, ht₂]
      rw [Valuation.map_mul, Valuation.map_mul, ht₂, hs₁]
      exact mul_lt_mul_of_pos_left hlt hm_pos
    have hR : v ((x₁ - x₂) * ((x₁ - x₀) ^ 2 + (x₁ - x₀) * (x₂ - x₀) + (x₂ - x₀) ^ 2))
        ≤ v (s₁ - s₂) * (m * m) := by
      rw [Valuation.map_mul, hvdx']; exact mul_le_mul' le_rfl hQ
    rw [← key, hL] at hR
    have : m * v (s₁ - s₂) ≤ (m * m) * v (s₁ - s₂) := by rwa [mul_comm (v (s₁ - s₂))] at hR
    have h1 : m * 1 ≤ m * m := by
      rw [mul_one]; exact le_of_mul_le_mul_right this hpos
    exact (not_le_of_gt hm1) (le_of_mul_le_mul_left h1 hm_pos)

theorem tangent_core (hx₀ : x₀ ∈ A) (hα : α ∈ A) (hβ : β ∈ A) (hαβ : v (α - β) = 1)
    (hsum : α + β = -(W.a₁ : L)) (hprod : α * β = -((W.a₂ : L) + 3 * x₀))
    (hFy : 2 * y₀ + (W.a₁ : L) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : L) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : L} (h : (E).toAffine.Nonsingular x y) (hX : v (x - x₀) < 1) (hY : v (y - y₀) < 1)
    (hm : v ((y - y₀) - α * (x - x₀)) = v ((y - y₀) - β * (x - x₀))) :
    (Point.some x y h + Point.some x y h : (E).toAffine.Point) = 0 ∨
      ∃ (x₃ y₃ : L) (h₃ : (E).toAffine.Nonsingular x₃ y₃),
        (Point.some x y h + Point.some x y h : (E).toAffine.Point) = Point.some x₃ y₃ h₃ ∧
          ¬ v (x₃ - x₀) < 1 := by
  by_cases hy : y = (E).toAffine.negY x y
  · exact Or.inl (add_self_of_Y_eq hy)
  right
  refine ⟨_, _, _, add_self_of_Y_ne hy, ?_⟩
  rw [slope_of_Y_ne rfl hy]
  set s := (y - y₀) - α * (x - x₀) with hs_def
  set t := (y - y₀) - β * (x - x₀) with ht_def
  set m := v s with hm_def

  have hden : y - (E).toAffine.negY x y = s + t := by
    rw [E_negY]; linear_combination (x - x₀) * hsum + hFy
  have hnum : 3 * x ^ 2 + 2 * (E).toAffine.a₂ * x + (E).toAffine.a₄ - (E).toAffine.a₁ * y
      = 3 * (x - x₀) ^ 2 + 2 * ((W.a₂ : L) + 3 * x₀) * (x - x₀) - (W.a₁ : L) * (y - y₀) := by
    rw [E_a₁, E_a₂, E_a₄]; linear_combination (-1 : L) * hFx
  have hden0 : s + t ≠ 0 := by rw [← hden]; exact sub_ne_zero.mpr hy
  set ℓ := (3 * x ^ 2 + 2 * (E).toAffine.a₂ * x + (E).toAffine.a₄ - (E).toAffine.a₁ * y)
    / (y - (E).toAffine.negY x y) with hℓ_def
  have hℓst : ℓ * (s + t)
      = 3 * (x - x₀) ^ 2 + 2 * ((W.a₂ : L) + 3 * x₀) * (x - x₀) - (W.a₁ : L) * (y - y₀) := by
    rw [hℓ_def, hden, hnum, div_mul_cancel₀ _ hden0]

  have htan : s * (ℓ - β) + t * (ℓ - α) = 3 * (x - x₀) ^ 2 := by
    have e : s * (ℓ - β) + t * (ℓ - α) = ℓ * (s + t) - (β * s + α * t) := by ring
    rw [e, hℓst, hs_def, ht_def]
    linear_combination (-(y - y₀)) * hsum + 2 * (x - x₀) * hprod

  have hkey : (E).toAffine.addX x x ℓ - x₀ = (ℓ - α) * (ℓ - β) - ((x - x₀) + (x - x₀)) := by
    rw [E_addX]; linear_combination ℓ * hsum - hprod
  have hm1 : m < 1 := val_s_lt_one hα hX hY
  have hXm : v (x - x₀) ≤ m := val_X_le hαβ le_rfl hm.symm.le
  have hX2 : v ((x - x₀) + (x - x₀)) < 1 := Valuation.map_add_lt _ hX hX
  by_cases hℓA : v ℓ ≤ 1
  ·
    have hℓα1 : v (ℓ - α) ≤ 1 := Valuation.map_sub_le _ hℓA (val_le_one_of_mem hα)
    have hℓβ1 : v (ℓ - β) ≤ 1 := Valuation.map_sub_le _ hℓA (val_le_one_of_mem hβ)
    have hm0 : m ≠ 0 := by
      intro hm0

      have hs0 : s = 0 := (Valuation.zero_iff _).mp hm0
      have ht0 : t = 0 := (Valuation.zero_iff _).mp (hm ▸ hm0)
      exact hden0 (by rw [hs0, ht0, add_zero])
    have hm_pos : 0 < m := lt_of_le_of_ne zero_le' (Ne.symm hm0)
    have h3X : v (3 * (x - x₀) ^ 2) < m := by
      rw [Valuation.map_mul, Valuation.map_pow, sq]
      have h3 : v (3 : L) ≤ 1 := by exact_mod_cast val_intCast_le_one (A := A) 3
      calc v (3 : L) * (v (x - x₀) * v (x - x₀)) ≤ 1 * (m * m) :=
            mul_le_mul' h3 (mul_le_mul' hXm hXm)
        _ = m * m := one_mul _
        _ < m * 1 := mul_lt_mul_of_pos_left hm1 hm_pos
        _ = m := mul_one _

    have hu : v (ℓ - α) = 1 ∧ v (ℓ - β) = 1 := by
      have hdiff : (ℓ - β) - (ℓ - α) = α - β := by ring
      by_contra hcon
      rcases not_and_or.mp hcon with hne | hne
      · have hlt : v (ℓ - α) < 1 := lt_of_le_of_ne hℓα1 hne

        have hu₂ : v (ℓ - β) = 1 := by
          refine le_antisymm hℓβ1 (not_lt.mp fun hlt₂ => ?_)
          have : v ((ℓ - β) - (ℓ - α)) < 1 := Valuation.map_sub_lt _ hlt₂ hlt
          rw [hdiff, hαβ] at this; exact lt_irrefl _ this

        have e1 : v (s * (ℓ - β)) = m := by rw [Valuation.map_mul, hu₂, mul_one]
        have e2 : v (t * (ℓ - α)) < m := by
          rw [Valuation.map_mul, ← hm]
          calc m * v (ℓ - α) < m * 1 := mul_lt_mul_of_pos_left hlt hm_pos
            _ = m := mul_one _
        have hL : v (s * (ℓ - β) + t * (ℓ - α)) = m := by
          rw [Valuation.map_add_eq_of_lt_left _ (by rw [e1]; exact e2), e1]
        rw [htan] at hL
        exact (lt_irrefl m) (hL ▸ h3X)
      · have hlt : v (ℓ - β) < 1 := lt_of_le_of_ne hℓβ1 hne
        have hu₁ : v (ℓ - α) = 1 := by
          refine le_antisymm hℓα1 (not_lt.mp fun hlt₁ => ?_)
          have : v ((ℓ - β) - (ℓ - α)) < 1 := Valuation.map_sub_lt _ hlt hlt₁
          rw [hdiff, hαβ] at this; exact lt_irrefl _ this
        have e1 : v (t * (ℓ - α)) = m := by rw [Valuation.map_mul, hu₁, mul_one, ← hm]
        have e2 : v (s * (ℓ - β)) < m := by
          rw [Valuation.map_mul]
          calc v s * v (ℓ - β) = m * v (ℓ - β) := rfl
            _ < m * 1 := mul_lt_mul_of_pos_left hlt hm_pos
            _ = m := mul_one _
        have hL : v (s * (ℓ - β) + t * (ℓ - α)) = m := by
          rw [Valuation.map_add_eq_of_lt_right _ (by rw [e1]; exact e2), e1]
        rw [htan] at hL
        exact (lt_irrefl m) (hL ▸ h3X)
    have : v ((E).toAffine.addX x x ℓ - x₀) = 1 := by
      rw [hkey, Valuation.map_sub_eq_of_lt_left, Valuation.map_mul, hu.1, hu.2, one_mul]
      rw [Valuation.map_mul, hu.1, hu.2, one_mul]; exact hX2
    rw [this]; exact lt_irrefl 1
  ·
    have hvℓ1 : 1 < v ℓ := not_le.mp hℓA
    have hxA : v x ≤ 1 := by
      have e : x = (x - x₀) + x₀ := by ring
      rw [e]; exact Valuation.map_add_le _ hX.le (val_le_one_of_mem hx₀)
    have hrest : v ((W.a₁ : L) * ℓ - (W.a₂ : L) - x - x) < v (ℓ ^ 2) := by
      rw [Valuation.map_pow, sq]
      have hℓℓ : v ℓ < v ℓ * v ℓ := lt_mul_self hvℓ1
      have h1ℓℓ : (1 : A.ValueGroup) < v ℓ * v ℓ := lt_trans hvℓ1 hℓℓ
      refine Valuation.map_sub_lt _ (Valuation.map_sub_lt _ (Valuation.map_sub_lt _ ?_ ?_) ?_) ?_
      · rw [Valuation.map_mul]
        calc v (W.a₁ : L) * v ℓ ≤ 1 * v ℓ := mul_le_mul' (val_intCast_le_one _) le_rfl
          _ = v ℓ := one_mul _
          _ < v ℓ * v ℓ := hℓℓ
      · exact lt_of_le_of_lt (val_intCast_le_one _) h1ℓℓ
      · exact lt_of_le_of_lt hxA h1ℓℓ
      · exact lt_of_le_of_lt hxA h1ℓℓ
    have hbig : 1 < v ((E).toAffine.addX x x ℓ) := by
      rw [E_addX]
      have e : ℓ ^ 2 + (W.a₁ : L) * ℓ - (W.a₂ : L) - x - x
          = ℓ ^ 2 + ((W.a₁ : L) * ℓ - (W.a₂ : L) - x - x) := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hrest, Valuation.map_pow, sq]
      exact lt_trans hvℓ1 (lt_mul_self hvℓ1)
    have : v ((E).toAffine.addX x x ℓ - x₀) = v ((E).toAffine.addX x x ℓ) :=
      Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt (val_le_one_of_mem hx₀) hbig)
    rw [this]
    exact not_lt.mpr hbig.le

end Frame

theorem exists_slopes {x₀ : L} (hx₀ : x₀ ∈ A) (hnode : v ((W.b₂ : L) + 12 * x₀) = 1) :
    ∃ α β : L, α ∈ A ∧ β ∈ A ∧ α + β = -(W.a₁ : L) ∧ α * β = -((W.a₂ : L) + 3 * x₀) ∧
      v (α - β) = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self ((W.b₂ : L) + 12 * x₀)
  have hb₂ : (W.b₂ : L) = (W.a₁ : L) ^ 2 + 4 * (W.a₂ : L) := by
    simp only [WeierstrassCurve.b₂]; push_cast; ring
  set a : L := (W.a₁ : L) with ha_def
  set b : L := (W.a₂ : L) + 3 * x₀ with hb_def
  have hz' : z * z = a ^ 2 + 4 * b := by rw [← hz, hb₂, hb_def]; ring
  have ha : a ∈ A := intCast_mem A _
  have h3 : (3 : L) ∈ A := by exact_mod_cast natCast_mem A 3
  have hb : b ∈ A := add_mem (intCast_mem A _) (mul_mem h3 hx₀)
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have h4 : (4 : L) ≠ 0 := by norm_num
  set α : L := (-a + z) / 2 with hα_def
  set β : L := (-a - z) / 2 with hβ_def
  have hrootα : α ^ 2 + a * α - b = 0 := by
    have e : α ^ 2 + a * α - b = (z * z - (a ^ 2 + 4 * b)) / 4 := by
      rw [hα_def]; field_simp; ring
    rw [e, hz', sub_self, zero_div]
  have hrootβ : β ^ 2 + a * β - b = 0 := by
    have e : β ^ 2 + a * β - b = (z * z - (a ^ 2 + 4 * b)) / 4 := by
      rw [hβ_def]; field_simp; ring
    rw [e, hz', sub_self, zero_div]
  refine ⟨α, β, mem_of_quadratic_root ha hb hrootα, mem_of_quadratic_root ha hb hrootβ,
    ?_, ?_, ?_⟩
  · rw [hα_def, hβ_def]; field_simp; ring
  · have e : α * β = (a ^ 2 - z * z) / 4 := by rw [hα_def, hβ_def]; field_simp; ring
    rw [e, hz']; field_simp; ring
  · have hαβ : α - β = z := by rw [hα_def, hβ_def]; field_simp; ring
    rw [hαβ]
    have hvz : v z * v z = 1 := by rw [← Valuation.map_mul, ← hz, hnode]
    exact eq_of_sq_eq_sq (by rw [hvz, one_mul])

end TFDispAnti

open TFDispAnti in

theorem solution
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - x₀) < 1)
    (hanti₁ : A.valuation (x₁ - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
    (hX₂ : A.valuation (x₂ - x₀) < 1)
    (hanti₂ : A.valuation (x₂ - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) :
    W.InZeroComponentAt A (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) := by

  obtain ⟨α, β, hα, hβ, hsum, hprod, hαβ⟩ := exists_slopes (W := W) (A := A) hx₀ hnode

  have key : ∀ (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      (x₃ y₃ : AlgebraicClosure ℚ)
      (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
      P = Point.some x₃ y₃ h₃ → ¬ A.valuation (x₃ - x₀) < 1 → W.InZeroComponentAt A P := by
    intro P x₃ y₃ h₃ hP hnot
    subst hP
    by_cases hx₃ : x₃ ∈ A
    · have hy₃ : y₃ ∈ A := y_mem_of_x_mem h₃.left hx₃
      have hunit : A.valuation (x₃ - x₀) = 1 :=
        le_antisymm (val_le_one_of_mem (sub_mem hx₃ hx₀)) (not_lt.mp hnot)
      exact WeierstrassCurve.inZeroComponentAt_of_valuation_sub_eq_one W A hx₀ hy₀ hFy hFx hbad
        h₃ hx₃ hy₃ hunit
    · exact Or.inr ⟨x₃, y₃, h₃, rfl, Or.inl hx₃⟩

  have hY₁ := val_Y_lt_one hx₀ hy₀ hα hβ hsum hprod hFy hFx hbad h₁.left hX₁
  have hY₂ := val_Y_lt_one hx₀ hy₀ hα hβ hsum hprod hFy hFx hbad h₂.left hX₂
  have hm₁ := val_s_eq_val_t_of_antipodal hαβ hsum hprod hFy hFx h₁.left hX₁ hanti₁
  have hm₂ := val_s_eq_val_t_of_antipodal hαβ hsum hprod hFy hFx h₂.left hX₂ hanti₂
  have hsq₁ := sq_eq_of_middle hα hαβ hsum hprod hFy hFx h₁.left hX₁ hY₁ hm₁
  have hsq₂ := sq_eq_of_middle hα hαβ hsum hprod hFy hFx h₂.left hX₂ hY₂ hm₂

  have hmm : A.valuation ((y₁ - y₀) - α * (x₁ - x₀)) = A.valuation ((y₂ - y₀) - α * (x₂ - x₀)) :=
    eq_of_sq_eq_sq (hsq₁.trans hsq₂.symm)
  have hm1 : A.valuation ((y₁ - y₀) - α * (x₁ - x₀)) < 1 := val_s_lt_one hα hX₁ hY₁

  have hΔ := val_ds_eq_val_dt_of_middle hαβ hsum hprod hFy hFx h₁.left h₂.left hm1
    rfl hm₁.symm hmm.symm (hm₂.symm.trans hmm.symm)
  by_cases hne : (y₁ - y₂) - α * (x₁ - x₂) = 0
  ·
    have hdt : (y₁ - y₂) - β * (x₁ - x₂) = 0 :=
      (Valuation.zero_iff _).mp (by rw [← hΔ, hne, Valuation.map_zero])
    have hβα : β - α ≠ 0 := by
      intro h0
      have : A.valuation (α - β) = 0 := by rw [Valuation.map_sub_swap, h0, Valuation.map_zero]
      rw [hαβ] at this; exact one_ne_zero this
    have hx : x₁ = x₂ := by
      have e : (β - α) * (x₁ - x₂)
          = ((y₁ - y₂) - α * (x₁ - x₂)) - ((y₁ - y₂) - β * (x₁ - x₂)) := by ring
      rw [hne, hdt, sub_zero] at e
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hβα)
    have hy : y₁ = y₂ := by
      rw [hx, sub_self, mul_zero, sub_zero] at hne
      exact sub_eq_zero.mp hne
    subst hx
    subst hy
    rcases tangent_core hx₀ hα hβ hαβ hsum hprod hFy hFx h₁ hX₁ hY₁ hm₁
      with h0 | ⟨x₃, y₃, h₃, hP, hnot⟩
    · exact Or.inl h0
    · exact key _ x₃ y₃ h₃ hP hnot
  ·
    have hy₁ : y₁ ∈ A := by
      have hx₁ : x₁ ∈ A := by
        have e : x₁ = (x₁ - x₀) + x₀ := by ring
        rw [e]; exact add_mem (mem_of_val_le_one hX₁.le) hx₀
      exact y_mem_of_x_mem h₁.left hx₁
    rcases WeierstrassCurve.node_chord_trichotomy W A hx₀ hα hsum hprod hαβ h₁ h₂ hX₁ hX₂ hy₁
      hΔ hne with h0 | ⟨x₃, y₃, h₃, hP, hx₃ | ⟨-, -, hunit, -⟩⟩
    · exact Or.inl h0
    · refine key _ x₃ y₃ h₃ hP fun hlt => hx₃ ?_
      have := add_mem (mem_of_val_le_one hlt.le) hx₀
      rwa [sub_add_cancel] at this
    · exact key _ x₃ y₃ h₃ hP (by rw [hunit]; exact lt_irrefl 1)

end S_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_add_of_antipodal (solution)
