-- Prove2me | solution 1 for WeierstrassCurve.level_add_of_antipodal_of_shallow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ce23db1d-8efd-5f44-8bab-77439f061ebe

import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_level_add_of_antipodal_of_shallow

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace AntiSh

noncomputable abbrev curve (W : WeierstrassCurve ℤ) : Affine (AlgebraicClosure ℚ) :=
  (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)

section coefficients

variable (W : WeierstrassCurve ℤ)

lemma curve_a₁ : (curve W).a₁ = (W.a₁ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₁) = _
  rw [eq_intCast, map_intCast]

lemma curve_a₂ : (curve W).a₂ = (W.a₂ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₂) = _
  rw [eq_intCast, map_intCast]

lemma curve_a₃ : (curve W).a₃ = (W.a₃ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₃) = _
  rw [eq_intCast, map_intCast]

lemma curve_a₄ : (curve W).a₄ = (W.a₄ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₄) = _
  rw [eq_intCast, map_intCast]

lemma curve_a₆ : (curve W).a₆ = (W.a₆ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₆) = _
  rw [eq_intCast, map_intCast]

lemma equation_iff_cast (x y : AlgebraicClosure ℚ) :
    (curve W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x * y + (W.a₃ : AlgebraicClosure ℚ) * y
        = x ^ 3 + (W.a₂ : AlgebraicClosure ℚ) * x ^ 2 + (W.a₄ : AlgebraicClosure ℚ) * x
          + (W.a₆ : AlgebraicClosure ℚ) := by
  rw [equation_iff]
  show y ^ 2 + (curve W).a₁ * x * y + (curve W).a₃ * y
      = x ^ 3 + (curve W).a₂ * x ^ 2 + (curve W).a₄ * x + (curve W).a₆ ↔ _
  rw [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]

lemma nonsingular_iff_cast (x y : AlgebraicClosure ℚ) :
    (curve W).toAffine.Nonsingular x y ↔ (curve W).toAffine.Equation x y ∧
      ((W.a₁ : AlgebraicClosure ℚ) * y - (3 * x ^ 2 + 2 * (W.a₂ : AlgebraicClosure ℚ) * x
          + (W.a₄ : AlgebraicClosure ℚ)) ≠ 0 ∨
        2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + (W.a₃ : AlgebraicClosure ℚ) ≠ 0) := by
  rw [nonsingular_iff']
  show (curve W).toAffine.Equation x y ∧
      ((curve W).a₁ * y - (3 * x ^ 2 + 2 * (curve W).a₂ * x + (curve W).a₄) ≠ 0 ∨
        2 * y + (curve W).a₁ * x + (curve W).a₃ ≠ 0) ↔ _
  rw [curve_a₁, curve_a₂, curve_a₃, curve_a₄]

lemma addX_cast (x₁ x₂ L : AlgebraicClosure ℚ) :
    (curve W).toAffine.addX x₁ x₂ L
      = L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ) - x₁ - x₂ := by
  show L ^ 2 + (curve W).a₁ * L - (curve W).a₂ - x₁ - x₂ = _
  rw [curve_a₁, curve_a₂]

lemma addY_cast (x₁ x₂ y₁ L : AlgebraicClosure ℚ) :
    (curve W).toAffine.addY x₁ x₂ y₁ L
      = -(L * ((curve W).toAffine.addX x₁ x₂ L - x₁) + y₁)
          - (W.a₁ : AlgebraicClosure ℚ) * (curve W).toAffine.addX x₁ x₂ L
          - (W.a₃ : AlgebraicClosure ℚ) := by
  show -(L * ((curve W).toAffine.addX x₁ x₂ L - x₁) + y₁)
      - (curve W).a₁ * (curve W).toAffine.addX x₁ x₂ L - (curve W).a₃ = _
  rw [curve_a₁, curve_a₃]

lemma b₂_cast : (W.b₂ : AlgebraicClosure ℚ) = (W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * W.a₂ := by
  simp only [WeierstrassCurve.b₂]; push_cast; ring

end coefficients

section valueGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

lemma lt_of_mul_self_lt {a b : Γ} (h : a * a < b * b) : a < b := by
  by_contra hle
  rw [not_lt] at hle
  exact (not_le.mpr h) (mul_le_mul' hle hle)

lemma le_of_mul_self_le {a b : Γ} (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  have ha : 0 < a := lt_of_le_of_lt zero_le' hlt
  have : b * b < a * a :=
    calc b * b ≤ a * b := mul_le_mul' hlt.le le_rfl
      _ < a * a := mul_lt_mul_of_pos_left hlt ha
  exact (not_lt.mpr h) this

lemma eq_one_of_mul_self_eq_one {a : Γ} (h : a * a = 1) : a = 1 :=
  (pow_eq_one_iff_left two_ne_zero).mp (by rw [sq]; exact h)

end valueGroup

section integrality

variable {L : Type*} [Field L] (A : ValuationSubring L)

lemma mem_of_monic_quadratic {a b z : L} (ha : a ∈ A) (hb : b ∈ A)
    (hz : z * z + a * z + b = 0) : z ∈ A := by
  by_contra hzA
  have hz1 : 1 < A.valuation z :=
    lt_of_not_ge fun h => hzA ((A.valuation_le_one_iff z).mp h)
  have hz0 : 0 < A.valuation z := lt_trans zero_lt_one hz1
  have hzz : A.valuation z < A.valuation (z * z) := by
    rw [Valuation.map_mul]
    calc A.valuation z = A.valuation z * 1 := (mul_one _).symm
      _ < A.valuation z * A.valuation z := mul_lt_mul_of_pos_left hz1 hz0
  have h1 : A.valuation (a * z) < A.valuation (z * z) := by
    refine lt_of_le_of_lt ?_ hzz
    rw [Valuation.map_mul]
    calc A.valuation a * A.valuation z ≤ 1 * A.valuation z :=
          mul_le_mul' ((A.valuation_le_one_iff a).mpr ha) le_rfl
      _ = A.valuation z := one_mul _
  have h2 : A.valuation b < A.valuation (z * z) :=
    lt_of_le_of_lt ((A.valuation_le_one_iff b).mpr hb) (hz1.trans hzz)
  have h3 : A.valuation (z * z + (a * z + b)) = A.valuation (z * z) :=
    Valuation.map_add_eq_of_lt_left _ (Valuation.map_add_lt _ h1 h2)
  rw [← add_assoc, hz, Valuation.map_zero] at h3
  exact (ne_of_lt (lt_trans hz0 hzz)) h3

end integrality

section chord

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "K" => AlgebraicClosure ℚ
local notation "v" => ValuationSubring.valuation A

theorem core {x₀ y₀ F₀ α β : K}
    (hFy : 2 * y₀ + (W.a₁ : K) * x₀ + W.a₃ = 0)
    (hsum : α + β = -(W.a₁ : K)) (hprod : α * β = -((W.a₂ : K) + 3 * x₀))
    (hαβ : v (α - β) = 1)
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hE₁ : (y₁ - y₀ - α * (x₁ - x₀)) * (y₁ - y₀ - β * (x₁ - x₀)) = (x₁ - x₀) ^ 3 - F₀)
    (hE₂ : (y₂ - y₀ - α * (x₂ - x₀)) * (y₂ - y₀ - β * (x₂ - x₀)) = (x₂ - x₀) ^ 3 - F₀)
    {u : A.ValueGroup} (hU₁ : v (y₁ - y₀ - α * (x₁ - x₀)) = u)
    (hV₁ : v (y₁ - y₀ - β * (x₁ - x₀)) = u) (huu : u * u = v F₀) (hu0 : 0 < u)
    (hf : v (x₁ - x₀) ≤ u)
    (hsh : v F₀ < v (x₂ - x₀) ^ 2) (hX₂ : v (x₂ - x₀) < 1)
    (hbr : v (y₂ - y₀ - α * (x₂ - x₀)) < v (x₂ - x₀)) :
    ∃ (x₃ y₃ : K) (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
      (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point)
          = Point.some x₃ y₃ h₃ ∧
        (v (x₃ - x₀) * v (x₂ - x₀)) ^ 2 = v F₀ ∧
        v ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1 := by

  set X₁ := x₁ - x₀ with hX₁def
  set X₂ := x₂ - x₀ with hX₂def
  set U₁ := y₁ - y₀ - α * (x₁ - x₀) with hU₁def
  set V₁ := y₁ - y₀ - β * (x₁ - x₀) with hV₁def
  set U₂ := y₂ - y₀ - α * (x₂ - x₀) with hU₂def
  set V₂ := y₂ - y₀ - β * (x₂ - x₀) with hV₂def
  set e := v X₂ with hedef

  have hu_lt_e : u < e := by
    apply lt_of_mul_self_lt; rw [huu, ← sq]; exact hsh
  have he0 : 0 < e := lt_trans hu0 hu_lt_e
  have he1 : e < 1 := hX₂
  have hf_lt_e : v X₁ < e := lt_of_le_of_lt hf hu_lt_e
  have hX₂0 : X₂ ≠ 0 := (Valuation.pos_iff _).mp he0
  have hx12 : x₁ ≠ x₂ := by
    intro h
    have : X₁ = X₂ := by rw [hX₁def, hX₂def, h]
    rw [this] at hf_lt_e
    exact lt_irrefl _ hf_lt_e
  have hX12 : X₁ - X₂ ≠ 0 := by
    rw [hX₁def, hX₂def]; intro h; apply hx12; linear_combination h
  have hvX12 : v (X₁ - X₂) = e := Valuation.map_sub_eq_of_lt_right _ hf_lt_e

  have hUV₂ : U₂ - V₂ = (β - α) * X₂ := by rw [hU₂def, hV₂def, hX₂def]; ring
  have hvβα : v (β - α) = 1 := by rw [← neg_sub, Valuation.map_neg]; exact hαβ
  have hvUV₂ : v (U₂ - V₂) = e := by rw [hUV₂, Valuation.map_mul, hvβα, one_mul, hedef]
  have hV₂ : v V₂ = e := by
    have h : V₂ = U₂ - (U₂ - V₂) := by ring
    have hlt : v U₂ < v (U₂ - V₂) := by rw [hvUV₂]; exact hbr
    rw [h, Valuation.map_sub_eq_of_lt_right _ hlt, hvUV₂]

  set ℓ := (curve W).toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  have hℓeq : ℓ = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx12
  have hℓX : ℓ * (X₁ - X₂) = (y₁ - y₀) - (y₂ - y₀) := by
    have h : X₁ - X₂ = x₁ - x₂ := by rw [hX₁def, hX₂def]; ring
    rw [h, hℓeq, div_mul_cancel₀ _ (sub_ne_zero.mpr hx12)]; ring
  have hℓα : ℓ - α = (U₁ - U₂) / (X₁ - X₂) := by
    rw [eq_div_iff hX12, sub_mul, hℓX, hU₁def, hU₂def, hX₁def, hX₂def]; ring
  have hℓβ : ℓ - β = (V₁ - V₂) / (X₁ - X₂) := by
    rw [eq_div_iff hX12, sub_mul, hℓX, hV₁def, hV₂def, hX₁def, hX₂def]; ring
  have hvℓα : v (ℓ - α) < 1 := by
    rw [hℓα, map_div₀, hvX12, div_lt_one₀ he0]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hbr)
    rw [hU₁]; exact hu_lt_e
  have hvV12 : v (V₁ - V₂) = e := by
    rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hV₁, hV₂]; exact hu_lt_e), hV₂]
  have hvℓβ : v (ℓ - β) = 1 := by
    rw [hℓβ, map_div₀, hvX12, hvV12, div_self (ne_of_gt he0)]
  have hv2ℓ : v (2 * ℓ + (W.a₁ : K)) = 1 := by
    have h : 2 * ℓ + (W.a₁ : K) = (ℓ - β) + (ℓ - α) := by linear_combination hsum
    rw [h, Valuation.map_add_eq_of_lt_left _ (by rw [hvℓβ]; exact hvℓα), hvℓβ]

  set ν := (y₁ - y₀) - ℓ * X₁ with hνdef
  have hνX : (X₁ - X₂) * ν = X₁ * U₂ - X₂ * U₁ := by
    rw [hνdef, hU₁def, hU₂def]
    linear_combination (-X₁) * hℓX
  have hvν : v ν = u := by
    have h1 : v (X₁ * U₂) < v (X₂ * U₁) := by
      rw [Valuation.map_mul, Valuation.map_mul, hU₁, ← hedef]
      calc v X₁ * v U₂ ≤ u * v U₂ := mul_le_mul' hf le_rfl
        _ < u * e := mul_lt_mul_of_pos_left hbr hu0
        _ = e * u := mul_comm _ _
    have h2 : v ((X₁ - X₂) * ν) = e * u := by
      rw [hνX, Valuation.map_sub_eq_of_lt_right _ h1, Valuation.map_mul, hU₁]
    rw [Valuation.map_mul, hvX12] at h2
    exact mul_left_cancel₀ (ne_of_gt he0) h2

  set X₃ := (curve W).toAffine.addX x₁ x₂ ℓ - x₀ with hX₃def
  have hX₃V1 : X₃ = (ℓ - α) * (ℓ - β) - X₁ - X₂ := by
    rw [hX₃def, addX_cast, hX₁def, hX₂def]
    linear_combination ℓ * hsum - hprod

  have hL₁ : (ℓ - α) * X₁ + ν = U₁ := by rw [hνdef, hU₁def, hX₁def]; ring
  have hL₁' : (ℓ - β) * X₁ + ν = V₁ := by rw [hνdef, hV₁def, hX₁def]; ring
  have hL₂ : (ℓ - α) * X₂ + ν = U₂ := by
    rw [hνdef, hU₂def, hX₂def]; linear_combination -hℓX
  have hL₂' : (ℓ - β) * X₂ + ν = V₂ := by
    rw [hνdef, hV₂def, hX₂def]; linear_combination -hℓX
  have hC₁ : ((ℓ - α) * X₁ + ν) * ((ℓ - β) * X₁ + ν) - X₁ ^ 3 + F₀ = 0 := by
    rw [hL₁, hL₁', hE₁]; ring
  have hC₂ : ((ℓ - α) * X₂ + ν) * ((ℓ - β) * X₂ + ν) - X₂ ^ 3 + F₀ = 0 := by
    rw [hL₂, hL₂', hE₂]; ring

  have hV2 : (X₁ + X₂) * X₃ = -(ν * (2 * ℓ + (W.a₁ : K))) - X₁ * X₂ := by
    have key : (X₁ - X₂) * ((X₁ + X₂) * X₃ + ν * (2 * ℓ + (W.a₁ : K)) + X₁ * X₂) = 0 := by
      rw [hX₃V1]
      linear_combination hC₁ - hC₂ + ((X₁ - X₂) * ν) * hsum
    have := (mul_eq_zero.mp key).resolve_left hX12
    linear_combination this

  have hvX1X2 : v (X₁ + X₂) = e := Valuation.map_add_eq_of_lt_right _ hf_lt_e
  have hvRHS : v (-(ν * (2 * ℓ + (W.a₁ : K))) - X₁ * X₂) = u := by
    have h1 : v (-(ν * (2 * ℓ + (W.a₁ : K)))) = u := by
      rw [Valuation.map_neg, Valuation.map_mul, hvν, hv2ℓ, mul_one]
    rw [Valuation.map_sub_eq_of_lt_left _ ?_, h1]
    rw [h1, Valuation.map_mul, ← hedef]
    calc v X₁ * e ≤ u * e := mul_le_mul' hf le_rfl
      _ < u * 1 := mul_lt_mul_of_pos_left he1 hu0
      _ = u := mul_one _
  have hvX₃ : v X₃ * e = u := by
    have h := congrArg (fun z => v z) hV2
    simp only [Valuation.map_mul, hvX1X2, hvRHS] at h
    rw [mul_comm] at h; exact h
  have hvX₃0 : 0 < v X₃ := by
    rcases eq_or_lt_of_le (zero_le' (a := v X₃)) with h | h
    · rw [← h, zero_mul] at hvX₃; exact absurd hvX₃ (ne_of_lt hu0)
    · exact h
  have hX₃0 : X₃ ≠ 0 := (Valuation.pos_iff _).mp hvX₃0
  have hu_lt_X₃ : u < v X₃ := by
    calc u = v X₃ * e := hvX₃.symm
      _ < v X₃ * 1 := mul_lt_mul_of_pos_left he1 hvX₃0
      _ = v X₃ := mul_one _

  set Y₃ := (curve W).toAffine.addY x₁ x₂ y₁ ℓ - y₀ with hY₃def
  have hY₃ : Y₃ = -(ℓ + (W.a₁ : K)) * X₃ - ν := by
    rw [hY₃def, addY_cast, hνdef, hX₃def, hX₁def]
    linear_combination -hFy

  rw [add_of_X_ne hx12]
  refine ⟨_, _, _, rfl, ?_, ?_⟩
  ·
    show (v ((curve W).toAffine.addX x₁ x₂ ℓ - x₀) * v (x₂ - x₀)) ^ 2 = v F₀
    rw [← hX₃def, ← hX₂def, ← hedef, hvX₃, sq, huu]
  ·
    show v (((curve W).toAffine.addY x₁ x₂ y₁ ℓ - y₀) / ((curve W).toAffine.addX x₁ x₂ ℓ - x₀)
        - (y₂ - y₀) / (x₂ - x₀)) = 1
    rw [← hX₃def, ← hY₃def, ← hX₂def]
    have hq : Y₃ / X₃ = -(ℓ + (W.a₁ : K)) - ν / X₃ := by
      rw [hY₃, sub_div, mul_div_cancel_right₀ _ hX₃0]
    have ht₃ : Y₃ / X₃ - β = -((ℓ - α) + ν / X₃) := by
      rw [hq]; linear_combination -hsum
    have ht₂ : (y₂ - y₀) / X₂ - β = V₂ / X₂ := by
      rw [eq_div_iff hX₂0, sub_mul, div_mul_cancel₀ _ hX₂0, hV₂def, hX₂def]
    have hvt₃ : v (Y₃ / X₃ - β) < 1 := by
      rw [ht₃, Valuation.map_neg]
      refine Valuation.map_add_lt _ hvℓα ?_
      rw [map_div₀, div_lt_one₀ hvX₃0, hvν]; exact hu_lt_X₃
    have hvt₂ : v ((y₂ - y₀) / X₂ - β) = 1 := by
      rw [ht₂, map_div₀, hV₂, hedef, div_self (ne_of_gt he0)]
    have h : Y₃ / X₃ - (y₂ - y₀) / X₂ = (Y₃ / X₃ - β) - ((y₂ - y₀) / X₂ - β) := by ring
    rw [h, Valuation.map_sub_eq_of_lt_right _ (by rw [hvt₂]; exact hvt₃), hvt₂]

theorem main {x₀ y₀ : K}
    (hFy : 2 * y₀ + (W.a₁ : K) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : K) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : v ((W.b₂ : K) + 12 * x₀) = 1)
    {x₁ y₁ x₂ y₂ : K}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - x₀) < 1)
    (hanti₁ : v (x₁ - x₀) ^ 2 ≤ v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
    (hX₂ : v (x₂ - x₀) < 1)
    (hsh₂ : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < v (x₂ - x₀) ^ 2) :
    ∃ (x₃ y₃ : K) (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
      (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point)
          = Point.some x₃ y₃ h₃ ∧
        (v (x₃ - x₀) * v (x₂ - x₀)) ^ 2 =
          v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) ∧
        v ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1 := by
  set F₀ : K := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
    - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hF₀

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self ((W.b₂ : K) + 12 * x₀)
  have hvr : v r = 1 :=
    eq_one_of_mul_self_eq_one (by rw [← Valuation.map_mul, ← hr]; exact hnode)
  set α : K := (-(W.a₁ : K) + r) / 2 with hαdef
  set β : K := (-(W.a₁ : K) - r) / 2 with hβdef
  have hsum : α + β = -(W.a₁ : K) := by rw [hαdef, hβdef]; ring
  have hαβr : α - β = r := by rw [hαdef, hβdef]; ring
  have hprod : α * β = -((W.a₂ : K) + 3 * x₀) := by
    have hb := b₂_cast W
    rw [hαdef, hβdef]
    linear_combination (1 / 4 : K) * hr - (1 / 4 : K) * hb
  have hvαβ : v (α - β) = 1 := by rw [hαβr]; exact hvr
  have hvβα : v (β - α) = 1 := by rw [← neg_sub, Valuation.map_neg]; exact hvαβ

  have hE : ∀ {x y : K}, (curve W).toAffine.Nonsingular x y →
      (y - y₀ - α * (x - x₀)) * (y - y₀ - β * (x - x₀)) = (x - x₀) ^ 3 - F₀ := by
    intro x y h
    have heq := (equation_iff_cast W x y).mp h.1
    rw [hF₀]
    linear_combination heq - (y - y₀) * hFy - (x - x₀) * hFx
      - ((x - x₀) * (y - y₀)) * hsum + (x - x₀) ^ 2 * hprod
  have hE₁ := hE h₁
  have hE₂ := hE h₂

  have hF₀0 : F₀ ≠ 0 := by
    intro h0
    have hX10 : x₁ - x₀ = 0 := by
      rw [h0, Valuation.map_zero] at hanti₁
      have h2 : v (x₁ - x₀) ^ 2 = 0 := le_antisymm hanti₁ zero_le'
      exact (Valuation.zero_iff _).mp ((pow_eq_zero_iff two_ne_zero).mp h2)
    have hx1 : x₁ = x₀ := by linear_combination hX10
    have hy1 : y₁ = y₀ := by
      have h := hE₁
      rw [hX10, h0] at h
      have h' : (y₁ - y₀) * (y₁ - y₀) = 0 := by linear_combination h
      linear_combination mul_self_eq_zero.mp h'
    have hns := (nonsingular_iff_cast W x₁ y₁).mp h₁
    rw [hx1, hy1] at hns
    rcases hns.2 with h | h
    · exact h (by linear_combination hFx)
    · exact h hFy
  have hD0 : 0 < v F₀ := (Valuation.pos_iff _).mpr hF₀0

  have hcube₁ : v ((x₁ - x₀) ^ 3) < v F₀ := by
    rw [Valuation.map_pow]
    have h3 : v (x₁ - x₀) ^ 3 = v (x₁ - x₀) ^ 2 * v (x₁ - x₀) := pow_succ _ 2
    rw [h3]
    calc v (x₁ - x₀) ^ 2 * v (x₁ - x₀) ≤ v F₀ * v (x₁ - x₀) := mul_le_mul' hanti₁ le_rfl
      _ < v F₀ * 1 := mul_lt_mul_of_pos_left hX₁ hD0
      _ = v F₀ := mul_one _
  have hUV₁ : v (y₁ - y₀ - α * (x₁ - x₀)) * v (y₁ - y₀ - β * (x₁ - x₀)) = v F₀ := by
    rw [← Valuation.map_mul, hE₁, Valuation.map_sub_eq_of_lt_right _ hcube₁]
  have hUmV₁ : (y₁ - y₀ - α * (x₁ - x₀)) - (y₁ - y₀ - β * (x₁ - x₀)) = (β - α) * (x₁ - x₀) := by
    ring
  have hvUmV₁ : v ((y₁ - y₀ - α * (x₁ - x₀)) - (y₁ - y₀ - β * (x₁ - x₀))) = v (x₁ - x₀) := by
    rw [hUmV₁, Valuation.map_mul, hvβα, one_mul]
  have hUeqV : v (y₁ - y₀ - α * (x₁ - x₀)) = v (y₁ - y₀ - β * (x₁ - x₀)) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    ·
      have hVf : v (y₁ - y₀ - β * (x₁ - x₀)) = v (x₁ - x₀) := by
        rw [← Valuation.map_sub_eq_of_lt_right _ hlt, hvUmV₁]
      have hV0 : 0 < v (y₁ - y₀ - β * (x₁ - x₀)) := by
        refine lt_of_le_of_ne zero_le' fun h => ?_
        rw [← h, mul_zero] at hUV₁
        exact (ne_of_lt hD0) hUV₁
      have : v F₀ < v F₀ :=
        calc v F₀ = _ := hUV₁.symm
          _ < v (y₁ - y₀ - β * (x₁ - x₀)) * v (y₁ - y₀ - β * (x₁ - x₀)) :=
              mul_lt_mul_of_pos_right hlt hV0
          _ = v (x₁ - x₀) ^ 2 := by rw [hVf, sq]
          _ ≤ v F₀ := hanti₁
      exact lt_irrefl _ this
    · have hUf : v (y₁ - y₀ - α * (x₁ - x₀)) = v (x₁ - x₀) := by
        rw [← Valuation.map_sub_eq_of_lt_left _ hlt, hvUmV₁]
      have hU0 : 0 < v (y₁ - y₀ - α * (x₁ - x₀)) := by
        refine lt_of_le_of_ne zero_le' fun h => ?_
        rw [← h, zero_mul] at hUV₁
        exact (ne_of_lt hD0) hUV₁
      have : v F₀ < v F₀ :=
        calc v F₀ = _ := hUV₁.symm
          _ < v (y₁ - y₀ - α * (x₁ - x₀)) * v (y₁ - y₀ - α * (x₁ - x₀)) :=
              mul_lt_mul_of_pos_left hlt hU0
          _ = v (x₁ - x₀) ^ 2 := by rw [hUf, sq]
          _ ≤ v F₀ := hanti₁
      exact lt_irrefl _ this
  set u := v (y₁ - y₀ - α * (x₁ - x₀)) with hudef
  have huu : u * u = v F₀ := by
    have h := hUV₁
    rw [← hUeqV] at h
    exact h
  have hu0 : 0 < u := by
    refine lt_of_le_of_ne zero_le' fun h => ?_
    rw [← h, zero_mul] at huu
    exact (ne_of_lt hD0) huu
  have hf : v (x₁ - x₀) ≤ u := by
    apply le_of_mul_self_le; rw [huu, ← sq]; exact hanti₁

  have he0 : 0 < v (x₂ - x₀) := by
    refine lt_of_le_of_ne zero_le' fun h => ?_
    rw [← h, zero_pow two_ne_zero] at hsh₂
    exact (not_lt.mpr zero_le') hsh₂
  have hcube₂ : v ((x₂ - x₀) ^ 3) < v (x₂ - x₀) ^ 2 := by
    rw [Valuation.map_pow]
    have h3 : v (x₂ - x₀) ^ 3 = v (x₂ - x₀) ^ 2 * v (x₂ - x₀) := pow_succ _ 2
    rw [h3]
    calc v (x₂ - x₀) ^ 2 * v (x₂ - x₀) < v (x₂ - x₀) ^ 2 * 1 :=
          mul_lt_mul_of_pos_left hX₂ (pow_pos he0 2)
      _ = v (x₂ - x₀) ^ 2 := mul_one _
  have hUV₂ : v (y₂ - y₀ - α * (x₂ - x₀)) * v (y₂ - y₀ - β * (x₂ - x₀)) < v (x₂ - x₀) ^ 2 := by
    rw [← Valuation.map_mul, hE₂]
    exact Valuation.map_sub_lt _ hcube₂ hsh₂
  have hdich : v (y₂ - y₀ - α * (x₂ - x₀)) < v (x₂ - x₀) ∨
      v (y₂ - y₀ - β * (x₂ - x₀)) < v (x₂ - x₀) := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    have : v (x₂ - x₀) ^ 2 ≤ v (y₂ - y₀ - α * (x₂ - x₀)) * v (y₂ - y₀ - β * (x₂ - x₀)) := by
      rw [sq]; exact mul_le_mul' hcon.1 hcon.2
    exact (not_lt.mpr this) hUV₂
  rcases hdich with hbr | hbr
  · exact core W A hFy hsum hprod hvαβ h₁ h₂ hE₁ hE₂ rfl hUeqV.symm huu hu0 hf hsh₂ hX₂ hbr
  · refine core W A hFy ((add_comm β α).trans hsum) ((mul_comm β α).trans hprod) hvβα h₁ h₂
      ?_ ?_ hUeqV.symm rfl huu hu0 hf hsh₂ hX₂ hbr
    · rw [mul_comm]; exact hE₁
    · rw [mul_comm]; exact hE₂

end chord

end AntiSh

open AntiSh in
set_option linter.unusedVariables false in
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
    (hsh₂ : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x₂ - x₀) ^ 2) :
    ∃ (x₃ y₃ : AlgebraicClosure ℚ)
      (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
      Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧
      (A.valuation (x₃ - x₀) * A.valuation (x₂ - x₀)) ^ 2 =
        A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) ∧
      A.valuation ((y₃ - y₀) / (x₃ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1 :=
  AntiSh.main W A hFy hFx hnode h₁ h₂ hX₁ hanti₁ hX₂ hsh₂

end S_WeierstrassCurve_level_add_of_antipodal_of_shallow
end P2MW
export P2MW.S_WeierstrassCurve_level_add_of_antipodal_of_shallow (solution)
