-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_of_valuation_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1b7d7ba8-44eb-541b-99fc-b3dcc66fe3ea

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_of_valuation_sub_eq_one

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace NodeChord

abbrev curve (W : WeierstrassCurve ℤ) : Affine (AlgebraicClosure ℚ) :=
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

lemma negY_cast (x y : AlgebraicClosure ℚ) :
    (curve W).toAffine.negY x y = -y - (W.a₁ : AlgebraicClosure ℚ) * x - (W.a₃ : AlgebraicClosure ℚ) := by
  show -y - (curve W).a₁ * x - (curve W).a₃ = _
  rw [curve_a₁, curve_a₃]

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

end coefficients

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "v" => ValuationSubring.valuation A

lemma mem_of_equation {x y : AlgebraicClosure ℚ} (h : (curve W).toAffine.Equation x y)
    (hx : x ∈ A) : y ∈ A := by
  rw [equation_iff_cast] at h
  by_contra hy
  have hvy : 1 < v y := lt_of_not_ge fun hle => hy ((A.valuation_le_one_iff y).mp hle)
  have hy0 : v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hvy)
  have ha₁ : v (W.a₁ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have ha₂ : v (W.a₂ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have ha₃ : v (W.a₃ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have ha₄ : v (W.a₄ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have ha₆ : v (W.a₆ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hxv : v x ≤ 1 := (A.valuation_le_one_iff x).mpr hx

  have hR : v (x ^ 3 + (W.a₂ : AlgebraicClosure ℚ) * x ^ 2 + (W.a₄ : AlgebraicClosure ℚ) * x
      + (W.a₆ : AlgebraicClosure ℚ)) ≤ 1 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ha₆
    · rw [map_pow]; exact pow_le_one₀ zero_le' hxv
    · rw [map_mul, map_pow]; exact mul_le_one' ha₂ (pow_le_one₀ zero_le' hxv)
    · rw [map_mul]; exact mul_le_one' ha₄ hxv

  have h2 : v y < v (y ^ 2) := by
    rw [map_pow, sq]
    calc v y = v y * 1 := (mul_one _).symm
      _ < v y * v y := mul_lt_mul_of_pos_left hvy (zero_lt_iff.mpr hy0)
  have hxy : v ((W.a₁ : AlgebraicClosure ℚ) * x * y) ≤ v y := by
    rw [map_mul, map_mul]
    calc v (W.a₁ : AlgebraicClosure ℚ) * v x * v y ≤ 1 * 1 * v y :=
          mul_le_mul' (mul_le_mul' ha₁ hxv) le_rfl
      _ = v y := by rw [one_mul, one_mul]
  have h3y : v ((W.a₃ : AlgebraicClosure ℚ) * y) ≤ v y := by
    rw [map_mul]
    calc v (W.a₃ : AlgebraicClosure ℚ) * v y ≤ 1 * v y := mul_le_mul' ha₃ le_rfl
      _ = v y := one_mul _
  have e1 : v (y ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x * y) = v (y ^ 2) :=
    Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hxy h2)
  have e2 : v (y ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * x * y + (W.a₃ : AlgebraicClosure ℚ) * y)
      = v (y ^ 2) := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [e1]; exact lt_of_le_of_lt h3y h2), e1]
  rw [h] at e2
  exact absurd (hvy.trans (h2.trans_le (e2 ▸ hR))) (lt_irrefl 1)

theorem node_chord_core {xs α β : AlgebraicClosure ℚ} (hxs : xs ∈ A) (hα : α ∈ A)
    (hsum : α + β = -(W.a₁ : AlgebraicClosure ℚ))
    (hprod : α * β = -((W.a₂ : AlgebraicClosure ℚ) + 3 * xs))
    (hαβ : v (α - β) = 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - xs) < 1) (hX₂ : v (x₂ - xs) < 1) (hy₁ : y₁ ∈ A)
    (hΔ : v ((y₁ - y₂) - α * (x₁ - x₂)) = v ((y₁ - y₂) - β * (x₁ - x₂)))
    (hne : (y₁ - y₂) - α * (x₁ - x₂) ≠ 0) :
    (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point) = 0 ∨
      ∃ (x₃ y₃ : AlgebraicClosure ℚ) (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point)
            = Point.some x₃ y₃ h₃ ∧
          (x₃ ∉ A ∨ (x₃ ∈ A ∧ y₃ ∈ A ∧ v (x₃ - xs) = 1 ∧
            v (x₁ - x₂) = v ((y₁ - y₂) - α * (x₁ - x₂)))) := by
  set Ds := (y₁ - y₂) - α * (x₁ - x₂) with hDs
  set Dt := (y₁ - y₂) - β * (x₁ - x₂) with hDt
  have hst : Ds - Dt = (β - α) * (x₁ - x₂) := by rw [hDs, hDt]; ring
  by_cases hx : x₁ = x₂
  ·
    rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with hy | hy
    · exfalso
      apply hne
      rw [hDs, hy, hx]
      ring
    · exact Or.inl (add_of_Y_eq hx hy)
  · right
    rw [add_of_X_ne hx]
    refine ⟨_, _, _, rfl, ?_⟩
    set L := (curve W).toAffine.slope x₁ x₂ y₁ y₂ with hL
    have hD0 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hLeq : L = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx
    have hLα : L - α = Ds / (x₁ - x₂) := by
      rw [eq_div_iff hD0, sub_mul, hLeq, div_mul_cancel₀ _ hD0]
    have hLβ : L - β = Dt / (x₁ - x₂) := by
      rw [eq_div_iff hD0, sub_mul, hLeq, div_mul_cancel₀ _ hD0]

    have hX₃ : (curve W).toAffine.addX x₁ x₂ L - xs = (L - α) * (L - β) - ((x₁ - xs) + (x₂ - xs)) := by
      rw [addX_cast]
      linear_combination L * hsum - hprod

    have ha₁ : v (W.a₁ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have ha₂ : v (W.a₂ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have hxsv : v xs ≤ 1 := (A.valuation_le_one_iff _).mpr hxs
    have hx₁A : x₁ ∈ A := by
      simpa using add_mem ((A.valuation_le_one_iff _).mp hX₁.le) hxs
    have hx₂A : x₂ ∈ A := by
      simpa using add_mem ((A.valuation_le_one_iff _).mp hX₂.le) hxs
    have hvD_pos : 0 < v (x₁ - x₂) := (Valuation.pos_iff _).mpr hD0
    have hvD_le : v (x₁ - x₂) ≤ v Ds := by
      have h := Valuation.map_sub (v) Ds Dt
      rw [hst, map_mul, Valuation.map_sub_swap, hαβ, one_mul, ← hΔ, max_self] at h
      exact h
    rcases hvD_le.lt_or_eq with hlt | heq
    ·
      left
      have hvLα : 1 < v (L - α) := by
        rw [hLα, map_div₀, one_lt_div₀ hvD_pos]; exact hlt
      have hvL : 1 < v L := by
        have hαv : v α ≤ 1 := (A.valuation_le_one_iff α).mpr hα
        have : L = (L - α) + α := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hαv hvLα)]
        exact hvLα
      have hvL0 : v L ≠ 0 := ne_of_gt (lt_trans zero_lt_one hvL)
      have hvL2 : v L < v (L ^ 2) := by
        rw [map_pow, sq]
        calc v L = v L * 1 := (mul_one _).symm
          _ < v L * v L := mul_lt_mul_of_pos_left hvL (zero_lt_iff.mpr hvL0)
      have h1L2 : 1 < v (L ^ 2) := hvL.trans hvL2
      have t1 : v ((W.a₁ : AlgebraicClosure ℚ) * L) < v (L ^ 2) := by
        rw [map_mul]
        calc v (W.a₁ : AlgebraicClosure ℚ) * v L ≤ 1 * v L := mul_le_mul' ha₁ le_rfl
          _ = v L := one_mul _
          _ < v (L ^ 2) := hvL2
      have e1 : v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L) = v (L ^ 2) :=
        Valuation.map_add_eq_of_lt_left _ t1
      have e2 : v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ))
          = v (L ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ (by rw [e1]; exact lt_of_le_of_lt ha₂ h1L2), e1]
      have hx₁lt : v x₁ < v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ)) := by
        rw [e2]; exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr hx₁A) h1L2
      have e3 : v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ) - x₁)
          = v (L ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ hx₁lt, e2]
      have hx₂lt : v x₂
          < v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ) - x₁) := by
        rw [e3]; exact lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr hx₂A) h1L2
      have e4 : v (L ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * L - (W.a₂ : AlgebraicClosure ℚ) - x₁ - x₂)
          = v (L ^ 2) := by
        rw [Valuation.map_sub_eq_of_lt_left _ hx₂lt, e3]
      intro hx₃A
      have hle : v ((curve W).toAffine.addX x₁ x₂ L) ≤ 1 := (A.valuation_le_one_iff _).mpr hx₃A
      rw [addX_cast, e4] at hle
      exact absurd (h1L2.trans_le hle) (lt_irrefl 1)
    ·
      right
      have hvD0 : v (x₁ - x₂) ≠ 0 := ne_of_gt hvD_pos
      have hvLα : v (L - α) = 1 := by rw [hLα, map_div₀, ← heq, div_self hvD0]
      have hvLβ : v (L - β) = 1 := by rw [hLβ, map_div₀, ← hΔ, ← heq, div_self hvD0]
      have hLA : L ∈ A := by
        simpa using add_mem ((A.valuation_le_one_iff _).mp hvLα.le) hα
      have hvsum : v ((x₁ - xs) + (x₂ - xs)) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hX₁ hX₂)
      have hvX₃ : v ((curve W).toAffine.addX x₁ x₂ L - xs) = 1 := by
        rw [hX₃, Valuation.map_sub_eq_of_lt_left _
          (by rw [map_mul, hvLα, hvLβ, one_mul]; exact hvsum), map_mul, hvLα, hvLβ, one_mul]
      have hx₃A : (curve W).toAffine.addX x₁ x₂ L ∈ A := by
        simpa using add_mem ((A.valuation_le_one_iff _).mp hvX₃.le) hxs
      have hy₃A : (curve W).toAffine.addY x₁ x₂ y₁ L ∈ A := by
        rw [addY_cast]
        exact sub_mem (sub_mem (neg_mem (add_mem (mul_mem hLA (sub_mem hx₃A hx₁A)) hy₁))
          (mul_mem (intCast_mem A _) hx₃A)) (intCast_mem A _)
      exact ⟨hx₃A, hy₃A, hvX₃, heq⟩

theorem inZeroComponentAt_of_valuation_sub_eq_one {xs ys : AlgebraicClosure ℚ}
    (hxs : xs ∈ A) (hys : ys ∈ A)
    (hFy : 2 * ys + (W.a₁ : AlgebraicClosure ℚ) * xs + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * ys = 3 * xs ^ 2 + 2 * W.a₂ * xs + W.a₄)
    (hbad : v (ys ^ 2 + W.a₁ * xs * ys + W.a₃ * ys
      - (xs ^ 3 + W.a₂ * xs ^ 2 + W.a₄ * xs + W.a₆)) < 1)
    {x y : AlgebraicClosure ℚ} (h : (curve W).toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A) (hunit : v (x - xs) = 1) :
    W.InZeroComponentAt A (Point.some x y h) := by
  refine Or.inr ⟨x, y, h, rfl, Or.inr ⟨hx, hy, ?_⟩⟩
  have heqK := (equation_iff_cast W x y).mp h.1
  have hF₀A : ys ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * xs * ys + (W.a₃ : AlgebraicClosure ℚ) * ys
      - (xs ^ 3 + (W.a₂ : AlgebraicClosure ℚ) * xs ^ 2 + (W.a₄ : AlgebraicClosure ℚ) * xs
        + (W.a₆ : AlgebraicClosure ℚ)) ∈ A :=
    (A.valuation_le_one_iff _).mp hbad.le

  have heqA : (⟨y, hy⟩ : A) ^ 2 + (W.a₁ : A) * ⟨x, hx⟩ * ⟨y, hy⟩ + (W.a₃ : A) * ⟨y, hy⟩
      = (⟨x, hx⟩ : A) ^ 3 + (W.a₂ : A) * (⟨x, hx⟩ : A) ^ 2 + (W.a₄ : A) * ⟨x, hx⟩ + (W.a₆ : A) := by
    apply Subtype.ext
    push_cast
    exact heqK
  have hidA : ((⟨x, hx⟩ : A) - ⟨xs, hxs⟩)
        * ((W.a₁ : A) * ⟨y, hy⟩ - (3 * (⟨x, hx⟩ : A) ^ 2 + 2 * (W.a₂ : A) * ⟨x, hx⟩ + (W.a₄ : A)))
      + ((⟨y, hy⟩ : A) - ⟨ys, hys⟩) * (2 * (⟨y, hy⟩ : A) + (W.a₁ : A) * ⟨x, hx⟩ + (W.a₃ : A))
      = -((⟨x, hx⟩ : A) - ⟨xs, hxs⟩) ^ 3 - 2 * (⟨_, hF₀A⟩ : A) := by
    apply Subtype.ext
    have h2 : ((2 : A) : AlgebraicClosure ℚ) = 2 := map_ofNat A.subtype 2
    have h3 : ((3 : A) : AlgebraicClosure ℚ) = 3 := map_ofNat A.subtype 3
    push_cast
    rw [h2, h3]
    linear_combination (2 : AlgebraicClosure ℚ) * heqK - (y - ys) * hFy - (x - xs) * hFx

  have hres0 : IsLocalRing.residue A ⟨_, hF₀A⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff _).mpr hbad
  have hresX : IsLocalRing.residue A ((⟨x, hx⟩ : A) - ⟨xs, hxs⟩) ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff] at h0
    have hlt := (A.valuation_lt_one_iff _).mp h0
    have hcoe : (((⟨x, hx⟩ : A) - ⟨xs, hxs⟩ : A) : AlgebraicClosure ℚ) = x - xs := rfl
    rw [hcoe, hunit] at hlt
    exact lt_irrefl _ hlt
  have heqk := congrArg (IsLocalRing.residue A) heqA
  have hidk := congrArg (IsLocalRing.residue A) hidA
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_intCast, map_ofNat, hres0,
    mul_zero, sub_zero] at heqk hidk
  rw [nonsingular_iff']
  refine ⟨?_, ?_⟩
  · rw [equation_iff]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast]
    exact heqk
  · simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, eq_intCast]
    by_contra hboth
    rw [not_or, not_ne_iff, not_ne_iff] at hboth
    obtain ⟨hFx0, hFy0⟩ := hboth
    rw [hFx0, hFy0, mul_zero, mul_zero, add_zero] at hidk

    have hcube : (IsLocalRing.residue A ⟨x, hx⟩ - IsLocalRing.residue A ⟨xs, hxs⟩) ^ 3 = 0 := by
      linear_combination hidk
    apply hresX
    rw [map_sub]
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube

lemma dichotomy {m n X : AlgebraicClosure ℚ} (hmn : v (m * n) < v X * v X)
    (hdiff : v (m - n) = v X) :
    (v m < v X ∧ v n = v X) ∨ (v n < v X ∧ v m = v X) := by
  rcases lt_or_ge (v m) (v X) with hm | hm
  · left
    refine ⟨hm, ?_⟩
    rcases lt_trichotomy (v n) (v X) with hn | hn | hn
    · exfalso
      have := Valuation.map_sub (v) m n
      rw [hdiff] at this
      exact absurd this (not_le.mpr (max_lt hm hn))
    · exact hn
    · exfalso
      rw [Valuation.map_sub_eq_of_lt_right _ (hm.trans hn)] at hdiff
      exact absurd hdiff (ne_of_gt hn)
  · right
    have hn : v n < v X := by
      by_contra hge
      rw [not_lt] at hge
      rw [map_mul] at hmn
      exact absurd hmn (not_lt.mpr (mul_le_mul' hm hge))
    refine ⟨hn, ?_⟩
    rw [Valuation.map_sub_eq_of_lt_left _ (hn.trans_le hm)] at hdiff
    exact hdiff

theorem ch_core {x₀ y₀ α β : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hbad : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    (hα : α ∈ A) (hsum : α + β = -(W.a₁ : AlgebraicClosure ℚ))
    (hprod : α * β = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀)) (hαβ : v (α - β) = 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - x₀) < 1) (hX₂ : v (x₂ - x₀) < 1) (hlev : v (x₁ - x₀) = v (x₂ - x₀))
    (hsh : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < v (x₁ - x₀) ^ 2)
    (hm₁ : v ((y₁ - y₀) - α * (x₁ - x₀)) < v (x₁ - x₀))
    (hm₂ : v ((y₂ - y₀) - α * (x₂ - x₀)) < v (x₂ - x₀)) :
    W.InZeroComponentAt A (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (curve W).toAffine.Point) = .some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - x₀)) := by

  have hx₁A : x₁ ∈ A := by simpa using add_mem ((A.valuation_le_one_iff _).mp hX₁.le) hx₀
  have hx₂A : x₂ ∈ A := by simpa using add_mem ((A.valuation_le_one_iff _).mp hX₂.le) hx₀
  have hy₁A : y₁ ∈ A := mem_of_equation W A h₁.1 hx₁A
  have hy₂A : y₂ ∈ A := mem_of_equation W A h₂.1 hx₂A
  have heq₁ := (equation_iff_cast W x₁ y₁).mp h₁.1
  have heq₂ := (equation_iff_cast W x₂ y₂).mp h₂.1

  have he0 : v (x₁ - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact absurd hsh (not_lt.mpr zero_le')
  have he0' : v (x₂ - x₀) ≠ 0 := hlev ▸ he0

  have key : ∀ {x y : AlgebraicClosure ℚ}, (curve W).toAffine.Equation x y →
      v (x - x₀) = v (x₁ - x₀) → v ((y - y₀) - α * (x - x₀)) < v (x - x₀) →
      v ((y - y₀) - β * (x - x₀)) = v (x - x₀) := by
    intro x y hxy hlv hm
    have heq := (equation_iff_cast W x y).mp hxy
    have hmn : ((y - y₀) - α * (x - x₀)) * ((y - y₀) - β * (x - x₀))
        = (x - x₀) ^ 3 - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
      linear_combination heq - (y - y₀) * hFy - (x - x₀) * hFx - (x - x₀) * (y - y₀) * hsum
        + (x - x₀) ^ 2 * hprod
    have hdf : ((y - y₀) - α * (x - x₀)) - ((y - y₀) - β * (x - x₀)) = (β - α) * (x - x₀) := by
      ring
    have hv0 : v (x - x₀) ≠ 0 := hlv ▸ he0
    have hvlt1 : v (x - x₀) < 1 := hlv ▸ hX₁
    have hvmn : v (((y - y₀) - α * (x - x₀)) * ((y - y₀) - β * (x - x₀)))
        < v (x - x₀) * v (x - x₀) := by
      rw [hmn]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · rw [map_pow, pow_succ, sq]
        calc v (x - x₀) * v (x - x₀) * v (x - x₀) < v (x - x₀) * v (x - x₀) * 1 :=
              mul_lt_mul_of_pos_left hvlt1 (mul_pos (zero_lt_iff.mpr hv0) (zero_lt_iff.mpr hv0))
          _ = v (x - x₀) * v (x - x₀) := mul_one _
      · rw [← sq, hlv]; exact hsh
    have hvdf : v (((y - y₀) - α * (x - x₀)) - ((y - y₀) - β * (x - x₀))) = v (x - x₀) := by
      rw [hdf, map_mul, Valuation.map_sub_swap, hαβ, one_mul]
    rcases dichotomy A hvmn hvdf with ⟨_, hn⟩ | ⟨_, hm'⟩
    · exact hn
    · exact absurd hm' (ne_of_lt hm)
  have hn₁ : v ((y₁ - y₀) - β * (x₁ - x₀)) = v (x₁ - x₀) := key h₁.1 rfl hm₁
  have hn₂ : v ((y₂ - y₀) - β * (x₂ - x₀)) = v (x₂ - x₀) := key h₂.1 hlev.symm hm₂

  have h₂' : (curve W).toAffine.Nonsingular x₂ ((curve W).toAffine.negY x₂ y₂) :=
    (nonsingular_neg ..).mpr h₂
  have hDs : (y₁ - (curve W).toAffine.negY x₂ y₂) - α * (x₁ - x₂)
      = ((y₁ - y₀) - α * (x₁ - x₀)) + ((y₂ - y₀) - β * (x₂ - x₀)) := by
    rw [negY_cast]
    linear_combination (x₂ - x₀) * hsum + hFy
  have hDt : (y₁ - (curve W).toAffine.negY x₂ y₂) - β * (x₁ - x₂)
      = ((y₁ - y₀) - β * (x₁ - x₀)) + ((y₂ - y₀) - α * (x₂ - x₀)) := by
    rw [negY_cast]
    linear_combination (x₂ - x₀) * hsum + hFy
  have hvDs : v ((y₁ - (curve W).toAffine.negY x₂ y₂) - α * (x₁ - x₂)) = v (x₁ - x₀) := by
    rw [hDs, Valuation.map_add_eq_of_lt_right _ (by rw [hn₂, ← hlev]; exact hm₁), hn₂, hlev]
  have hvDt : v ((y₁ - (curve W).toAffine.negY x₂ y₂) - β * (x₁ - x₂)) = v (x₁ - x₀) := by
    rw [hDt, Valuation.map_add_eq_of_lt_left _ (by rw [hn₁, hlev]; exact hm₂), hn₁]
  have hΔ : v ((y₁ - (curve W).toAffine.negY x₂ y₂) - α * (x₁ - x₂))
      = v ((y₁ - (curve W).toAffine.negY x₂ y₂) - β * (x₁ - x₂)) := by rw [hvDs, hvDt]
  have hne : (y₁ - (curve W).toAffine.negY x₂ y₂) - α * (x₁ - x₂) ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hvDs
    exact he0 hvDs.symm
  have hsub : (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (curve W).toAffine.Point)
      = Point.some x₁ y₁ h₁ + Point.some x₂ ((curve W).toAffine.negY x₂ y₂) h₂' := by
    rw [sub_eq_add_neg, neg_some]
  rcases node_chord_core W A hx₀ hα hsum hprod hαβ h₁ h₂' hX₁ hX₂ hy₁A hΔ hne with
    h0 | ⟨x₃, y₃, h₃, h3eq, hpole | ⟨hx₃, hy₃, hunit, hsharp⟩⟩
  ·
    refine ⟨Or.inl (hsub.trans h0), ?_⟩
    intro x₃ y₃ h₃ h hx₃
    exact absurd ((h.symm.trans (hsub.trans h0))) (some_ne_zero h₃)
  ·
    refine ⟨Or.inr ⟨x₃, y₃, h₃, hsub.trans h3eq, Or.inl hpole⟩, ?_⟩
    intro x₃' y₃' h₃' h hx₃'
    have hxx : x₃ = x₃' := (some.injEq _ _ _ _ _ _).mp ((hsub.trans h3eq).symm.trans h) |>.1
    exact absurd (hxx ▸ hx₃') hpole
  ·
    refine ⟨?_, fun _ _ _ => by rw [hsharp, hvDs]⟩
    rw [hsub, h3eq]
    exact inZeroComponentAt_of_valuation_sub_eq_one W A hx₀ hy₀ hFy hFx hbad h₃ hx₃ hy₃ hunit

lemma exists_tangent_slopes {x₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A)
    (hnode : v ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1) :
    ∃ α β : AlgebraicClosure ℚ, α ∈ A ∧ β ∈ A ∧ α + β = -(W.a₁ : AlgebraicClosure ℚ) ∧
      α * β = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) ∧ v (α - β) = 1 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) two_pos
  have hb₂ : (W.b₂ : AlgebraicClosure ℚ) = (W.a₁ : AlgebraicClosure ℚ) ^ 2 + 4 * W.a₂ := by
    show ((W.a₁ ^ 2 + 4 * W.a₂ : ℤ) : AlgebraicClosure ℚ) = _
    push_cast
    ring
  set α := (-(W.a₁ : AlgebraicClosure ℚ) + δ) / 2 with hαdef
  set β := (-(W.a₁ : AlgebraicClosure ℚ) - δ) / 2 with hβdef
  have h2 : (2 : AlgebraicClosure ℚ) ≠ 0 := two_ne_zero
  have hsum : α + β = -(W.a₁ : AlgebraicClosure ℚ) := by
    rw [hαdef, hβdef]; field_simp; ring
  have hdiff : α - β = δ := by rw [hαdef, hβdef]; field_simp; ring
  have hprod : α * β = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) := by
    rw [hαdef, hβdef]
    field_simp
    linear_combination -hδ - hb₂
  have hvδ : v δ = 1 := by
    have h2' : v δ ^ 2 = 1 := by rw [← map_pow, hδ]; exact hnode
    rcases lt_trichotomy (v δ) 1 with hlt | heq | hgt
    · exact absurd h2' (ne_of_lt (pow_lt_one₀ zero_le' hlt two_ne_zero))
    · exact heq
    · exact absurd h2' (ne_of_gt (one_lt_pow₀ hgt two_ne_zero))

  have ha₁ : v (W.a₁ : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hcA : v ((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (add_mem (intCast_mem A _)
      (mul_mem (ofNat_mem A 3) hx₀))
  have hαA : α ∈ A := by
    by_contra hαA
    have hvα : 1 < v α := lt_of_not_ge fun hle => hαA ((A.valuation_le_one_iff α).mp hle)
    have hα0 : v α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hvα)
    have hroot : α ^ 2 = -(W.a₁ : AlgebraicClosure ℚ) * α + ((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) := by
      linear_combination α * hsum - hprod
    have hlt2 : v α < v (α ^ 2) := by
      rw [map_pow, sq]
      calc v α = v α * 1 := (mul_one _).symm
        _ < v α * v α := mul_lt_mul_of_pos_left hvα (zero_lt_iff.mpr hα0)
    have hr : v (-(W.a₁ : AlgebraicClosure ℚ) * α + ((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀)) < v (α ^ 2) := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ (lt_of_le_of_lt hcA (hvα.trans hlt2)))
      rw [map_mul, Valuation.map_neg]
      calc v (W.a₁ : AlgebraicClosure ℚ) * v α ≤ 1 * v α := mul_le_mul' ha₁ le_rfl
        _ = v α := one_mul _
        _ < v (α ^ 2) := hlt2
    rw [← hroot] at hr
    exact lt_irrefl _ hr
  have hβA : β ∈ A := by
    have : β = -(W.a₁ : AlgebraicClosure ℚ) - α := by linear_combination hsum
    rw [this]
    exact sub_mem (neg_mem (intCast_mem A _)) hαA
  exact ⟨α, β, hαA, hβA, hsum, hprod, hdiff ▸ hvδ⟩

theorem ch_eq {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : v ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - x₀) < 1) (hX₂ : v (x₂ - x₀) < 1)
    (hlev : v (x₁ - x₀) = v (x₂ - x₀))
    (hsh : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < v (x₁ - x₀) ^ 2)
    (hbr : v ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) < 1) :
    W.InZeroComponentAt A (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂ : (curve W).toAffine.Point) = .some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - x₀)) := by
  obtain ⟨α, β, hαA, hβA, hsum, hprod, hαβ⟩ := exists_tangent_slopes W A hx₀ hnode
  have heq₁ := (equation_iff_cast W x₁ y₁).mp h₁.1

  have he0 : v (x₁ - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact absurd hsh (not_lt.mpr zero_le')
  have hX₁0 : x₁ - x₀ ≠ 0 := (Valuation.ne_zero_iff _).mp he0
  have hX₂0 : x₂ - x₀ ≠ 0 := (Valuation.ne_zero_iff _).mp (hlev ▸ he0)

  have hmn : ((y₁ - y₀) - α * (x₁ - x₀)) * ((y₁ - y₀) - β * (x₁ - x₀))
      = (x₁ - x₀) ^ 3 - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
    linear_combination heq₁ - (y₁ - y₀) * hFy - (x₁ - x₀) * hFx - (x₁ - x₀) * (y₁ - y₀) * hsum
      + (x₁ - x₀) ^ 2 * hprod
  have hvmn : v (((y₁ - y₀) - α * (x₁ - x₀)) * ((y₁ - y₀) - β * (x₁ - x₀)))
      < v (x₁ - x₀) * v (x₁ - x₀) := by
    rw [hmn]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_pow, pow_succ, sq]
      calc v (x₁ - x₀) * v (x₁ - x₀) * v (x₁ - x₀) < v (x₁ - x₀) * v (x₁ - x₀) * 1 :=
            mul_lt_mul_of_pos_left hX₁ (mul_pos (zero_lt_iff.mpr he0) (zero_lt_iff.mpr he0))
        _ = v (x₁ - x₀) * v (x₁ - x₀) := mul_one _
    · rw [← sq]; exact hsh
  have hvdf : v (((y₁ - y₀) - α * (x₁ - x₀)) - ((y₁ - y₀) - β * (x₁ - x₀))) = v (x₁ - x₀) := by
    rw [show ((y₁ - y₀) - α * (x₁ - x₀)) - ((y₁ - y₀) - β * (x₁ - x₀)) = (β - α) * (x₁ - x₀) by ring,
      map_mul, Valuation.map_sub_swap, hαβ, one_mul]

  have transfer : ∀ {γ : AlgebraicClosure ℚ}, v ((y₁ - y₀) - γ * (x₁ - x₀)) < v (x₁ - x₀) →
      v ((y₂ - y₀) - γ * (x₂ - x₀)) < v (x₂ - x₀) := by
    intro γ hγ
    have hid : (y₂ - y₀) - γ * (x₂ - x₀) = (x₂ - x₀) *
        (((y₁ - y₀) - γ * (x₁ - x₀)) / (x₁ - x₀) - ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀))) := by
      field_simp
      ring
    rw [hid, map_mul]
    calc v (x₂ - x₀) * v (((y₁ - y₀) - γ * (x₁ - x₀)) / (x₁ - x₀)
          - ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)))
        < v (x₂ - x₀) * 1 := by
          refine mul_lt_mul_of_pos_left ?_ (zero_lt_iff.mpr (hlev ▸ he0))
          refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hbr)
          rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr he0)]
          exact hγ
      _ = v (x₂ - x₀) := mul_one _
  rcases dichotomy A hvmn hvdf with ⟨hm₁, _⟩ | ⟨hn₁, _⟩
  · exact ch_core W A hx₀ hy₀ hFy hFx hbad hαA hsum hprod hαβ h₁ h₂ hX₁ hX₂ hlev hsh hm₁
      (transfer hm₁)
  · have hsum' : β + α = -(W.a₁ : AlgebraicClosure ℚ) := by rw [add_comm]; exact hsum
    have hprod' : β * α = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) := by rw [mul_comm]; exact hprod
    have hβα : v (β - α) = 1 := by rw [Valuation.map_sub_swap]; exact hαβ
    exact ch_core W A hx₀ hy₀ hFy hFx hbad hβA hsum' hprod' hβα h₁ h₂ hX₁ hX₂ hlev hsh hn₁
      (transfer hn₁)

theorem ch_pm {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : v ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : (curve W).toAffine.Nonsingular x₁ y₁) (h₂ : (curve W).toAffine.Nonsingular x₂ y₂)
    (hX₁ : v (x₁ - x₀) < 1) (hX₂ : v (x₂ - x₀) < 1)
    (hlev : v (x₁ - x₀) = v (x₂ - x₀))
    (hsh : v (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < v (x₁ - x₀) ^ 2)
    (hbr : v ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) = 1) :
    W.InZeroComponentAt A (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point) = .some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - x₀)) := by
  obtain ⟨α, β, hαA, hβA, hsum, hprod, hαβ⟩ := exists_tangent_slopes W A hx₀ hnode
  have heq₁ := (equation_iff_cast W x₁ y₁).mp h₁.1
  have heq₂ := (equation_iff_cast W x₂ y₂).mp h₂.1
  have he0 : v (x₁ - x₀) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsh
    exact absurd hsh (not_lt.mpr zero_le')
  have he0' : v (x₂ - x₀) ≠ 0 := hlev ▸ he0
  have hX₁0 : x₁ - x₀ ≠ 0 := (Valuation.ne_zero_iff _).mp he0
  have hX₂0 : x₂ - x₀ ≠ 0 := (Valuation.ne_zero_iff _).mp he0'

  have facts : ∀ {x y : AlgebraicClosure ℚ}, (curve W).toAffine.Equation x y →
      v (x - x₀) = v (x₁ - x₀) → ∀ {γ γ' : AlgebraicClosure ℚ}, γ + γ' = -(W.a₁ : AlgebraicClosure ℚ) →
      γ * γ' = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) → v (γ - γ') = 1 →
      (v ((y - y₀) - γ * (x - x₀)) < v (x - x₀) ∨ v ((y - y₀) - γ' * (x - x₀)) < v (x - x₀)) := by
    intro x y hxy hlv γ γ' hs hp hu
    have heq := (equation_iff_cast W x y).mp hxy
    have hv0 : v (x - x₀) ≠ 0 := hlv ▸ he0
    have hvlt1 : v (x - x₀) < 1 := hlv ▸ hX₁
    have hmn : ((y - y₀) - γ * (x - x₀)) * ((y - y₀) - γ' * (x - x₀))
        = (x - x₀) ^ 3 - (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
          - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
      linear_combination heq - (y - y₀) * hFy - (x - x₀) * hFx - (x - x₀) * (y - y₀) * hs
        + (x - x₀) ^ 2 * hp
    have hvmn : v (((y - y₀) - γ * (x - x₀)) * ((y - y₀) - γ' * (x - x₀)))
        < v (x - x₀) * v (x - x₀) := by
      rw [hmn]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · rw [map_pow, pow_succ, sq]
        calc v (x - x₀) * v (x - x₀) * v (x - x₀) < v (x - x₀) * v (x - x₀) * 1 :=
              mul_lt_mul_of_pos_left hvlt1 (mul_pos (zero_lt_iff.mpr hv0) (zero_lt_iff.mpr hv0))
          _ = v (x - x₀) * v (x - x₀) := mul_one _
      · rw [← sq, hlv]; exact hsh
    have hvdf : v (((y - y₀) - γ * (x - x₀)) - ((y - y₀) - γ' * (x - x₀))) = v (x - x₀) := by
      rw [show ((y - y₀) - γ * (x - x₀)) - ((y - y₀) - γ' * (x - x₀)) = (γ' - γ) * (x - x₀) by ring,
        map_mul, Valuation.map_sub_swap, hu, one_mul]
    rcases dichotomy A hvmn hvdf with ⟨hm, _⟩ | ⟨hn, _⟩
    · exact Or.inl hm
    · exact Or.inr hn

  have h₂' : (curve W).toAffine.Nonsingular x₂ ((curve W).toAffine.negY x₂ y₂) :=
    (nonsingular_neg ..).mpr h₂
  have hneg : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point)
      = Point.some x₁ y₁ h₁ - Point.some x₂ ((curve W).toAffine.negY x₂ y₂) h₂' := by
    rw [sub_eq_add_neg, neg_some]
    congr 2
    exact (negY_negY x₂ y₂).symm

  have main : ∀ {γ γ' : AlgebraicClosure ℚ}, γ ∈ A → γ + γ' = -(W.a₁ : AlgebraicClosure ℚ) →
      γ * γ' = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) → v (γ - γ') = 1 →
      v ((y₁ - y₀) - γ * (x₁ - x₀)) < v (x₁ - x₀) →
      W.InZeroComponentAt A (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∧
      (∀ {x₃ y₃ : AlgebraicClosure ℚ} (h₃ : (curve W).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : (curve W).toAffine.Point) = .some x₃ y₃ h₃ →
          x₃ ∈ A → v (x₁ - x₂) = v (x₁ - x₀)) := by
    intro γ γ' hγA hs hp hu hm₁

    have hn₂ : v ((y₂ - y₀) - γ' * (x₂ - x₀)) < v (x₂ - x₀) := by
      rcases facts h₂.1 hlev.symm hs hp hu with hm₂ | hn₂
      · exfalso

        have hid : (y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)
            = ((y₁ - y₀) - γ * (x₁ - x₀)) / (x₁ - x₀) - ((y₂ - y₀) - γ * (x₂ - x₀)) / (x₂ - x₀) := by
          field_simp
          ring
        have hlt : v ((y₁ - y₀) / (x₁ - x₀) - (y₂ - y₀) / (x₂ - x₀)) < 1 := by
          rw [hid]
          refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
          · rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr he0)]; exact hm₁
          · rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr he0')]; exact hm₂
        rw [hbr] at hlt
        exact lt_irrefl _ hlt
      · exact hn₂

    have hmQ : v (((curve W).toAffine.negY x₂ y₂ - y₀) - γ * (x₂ - x₀)) < v (x₂ - x₀) := by
      have hid : ((curve W).toAffine.negY x₂ y₂ - y₀) - γ * (x₂ - x₀)
          = -((y₂ - y₀) - γ' * (x₂ - x₀)) := by
        rw [negY_cast]
        linear_combination -(x₂ - x₀) * hs - hFy
      rw [hid, Valuation.map_neg]
      exact hn₂
    have res := ch_core W A hx₀ hy₀ hFy hFx hbad hγA hs hp hu h₁ h₂' hX₁ hX₂ hlev hsh hm₁ hmQ
    rw [← hneg] at res
    exact res
  rcases facts h₁.1 rfl hsum hprod hαβ with hm₁ | hn₁
  · exact main hαA hsum hprod hαβ hm₁
  · have hsum' : β + α = -(W.a₁ : AlgebraicClosure ℚ) := by rw [add_comm]; exact hsum
    have hprod' : β * α = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀) := by rw [mul_comm]; exact hprod
    have hβα : v (β - α) = 1 := by rw [Valuation.map_sub_swap]; exact hαβ
    exact main hβA hsum' hprod' hβα hn₁

end NodeChord

theorem solution
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A) (hunit : A.valuation (x - x₀) = 1) :
    W.InZeroComponentAt A (.some x y h) :=
  NodeChord.inZeroComponentAt_of_valuation_sub_eq_one W A hx₀ hy₀ hFy hFx hbad h hx hy hunit

end

end S_WeierstrassCurve_inZeroComponentAt_of_valuation_sub_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_of_valuation_sub_eq_one (solution)
