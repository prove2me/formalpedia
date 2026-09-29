-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.addGroup_fg_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/176d786f-60bc-5419-829c-57e32b82514c

import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.GroupTheory.Descent
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex

set_option autoImplicit false

p2m_open "Height P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.Height"

namespace Rat
p2m_export "Rat" "reduced den num le_ceil num_div_den mulHeight₁_eq_max"
p2m_open "Rat"

theorem finite_setOf_mulHeight₁_le (b : ℝ) : {q : ℚ | mulHeight₁ q ≤ b}.Finite := by
  set N : ℕ := ⌈b⌉₊ with hN
  have key : {q : ℚ | mulHeight₁ q ≤ b} ⊆
      (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)) ''
        (Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc 0 N) := by
    intro q hq
    rw [Set.mem_setOf_eq, Rat.mulHeight₁_eq_max] at hq
    have hmax : max q.num.natAbs q.den ≤ N := by
      exact_mod_cast hq.trans (Nat.le_ceil b)
    have hnum : q.num.natAbs ≤ N := le_trans (le_max_left _ _) hmax
    have hden : q.den ≤ N := le_trans (le_max_right _ _) hmax
    refine ⟨(q.num, q.den), ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_Icc]
      omega
    · exact ⟨Nat.zero_le _, hden⟩
    · simpa using Rat.num_div_den q
  exact Set.Finite.subset (Set.Finite.image _ ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))) key

theorem finite_setOf_logHeight₁_le (b : ℝ) : {q : ℚ | logHeight₁ q ≤ b}.Finite := by
  refine (finite_setOf_mulHeight₁_le (Real.exp b)).subset fun q hq => ?_
  rw [Set.mem_setOf_eq, logHeight₁_eq_log_mulHeight₁] at hq
  rw [Set.mem_setOf_eq, ← Real.exp_log (mulHeight₁_pos q)]
  exact Real.exp_le_exp.mpr hq

end Rat

scoped instance instNorthcottRatMulHeight : Northcott (mulHeight₁ : ℚ → ℝ) :=
  ⟨Rat.finite_setOf_mulHeight₁_le⟩

scoped instance instNorthcottRatLogHeight : Northcott (logHeight₁ : ℚ → ℝ) :=
  ⟨Rat.finite_setOf_logHeight₁_le⟩

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map b₂ Ψ₂Sq a₄ a₂ a₆ reduction Affine.Point b₆ b₈ Δ j b₄"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.eq_or_eq_neg_of_xRep_eq_xRep Equation negY slope_of_X_ne Point.xRep_some slope map Point.some Point.X_eq_iff Nonsingular Point.add_self_of_Y_eq Point.zero_def nonsingular_add slope_of_Y_ne Point addX nonsingular_neg Point.add_of_X_ne equation_iff polynomial Point.zero Point.neg_some Point.add_self_of_Y_ne"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F] {W : Affine F}

variable (W) in

private def _root_.WeierstrassCurve.Affine.xCoord : W.Point → F
  | .zero => 0
  | .some x _ _ => x

p2m_export "WeierstrassCurve.Affine" "xCoord"
@[scoped simp]
lemma xCoord_zero : W.xCoord .zero = 0 :=
  rfl

@[scoped simp]
lemma xCoord_some {x y : F} (h : W.Nonsingular x y) : W.xCoord (.some x y h) = x :=
  rfl

theorem finite_preimage_xCoord (c : F) : (W.xCoord ⁻¹' {c}).Finite := by
  by_cases hex : ∃ P ∈ W.xCoord ⁻¹' {c}, P ≠ Point.zero
  · obtain ⟨Q, hQ, hQ0⟩ := hex
    refine (((Set.finite_singleton (-Q)).insert Q).insert Point.zero).subset fun P hP => ?_
    rcases eq_or_ne P Point.zero with rfl | hP0
    · exact Set.mem_insert _ _
    ·

      rcases P with _ | ⟨xP, yP, hP'⟩
      · exact absurd rfl hP0
      rcases Q with _ | ⟨xQ, yQ, hQ'⟩
      · exact absurd rfl hQ0
      have hxP : xP = c := by simpa using hP
      have hxQ : xQ = c := by simpa using hQ
      have hrep : (Point.some xP yP hP').xRep = (Point.some xQ yQ hQ').xRep := by
        rw [Point.xRep_some, Point.xRep_some, hxP, hxQ]
      rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hrep with heq | heq
      · rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · push Not at hex
    exact (Set.finite_singleton Point.zero).subset fun P hP => hex P hP

section Rat

variable {W : Affine ℚ}

scoped instance instNorthcottLogHeightXCoord : Northcott (logHeight₁ ∘ W.xCoord) :=
  haveI : Filter.TendstoCofinite W.xCoord :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xCoord
  Northcott.comp_of_finite_fibers W.xCoord logHeight₁

namespace Point p2m_export "WeierstrassCurve.Affine.Point" "eq_or_eq_neg_of_xRep_eq_xRep xRep_some xRep_eq_xRep_iff some X_eq_iff add_self_of_Y_eq zero_def xRep map some_ne_zero add_of_X_ne zero neg_some add_self_of_Y_ne" end Point
namespace Point
p2m_open_scoped "WeierstrassCurve.Affine.Point" in

private noncomputable def _root_.WeierstrassCurve.Affine.Point.weilHeight (P : W.Point) : ℝ :=
  logHeight₁ (W.xCoord P)

end Point
p2m_export "WeierstrassCurve.Affine" "Point.weilHeight"
p2m_open_scoped "WeierstrassCurve.Affine.Point" in
lemma Point.weilHeight_zero : (Point.zero : W.Point).weilHeight = 0 := by
  simp [Point.weilHeight]

p2m_open_scoped "WeierstrassCurve.Affine.Point" in
lemma Point.weilHeight_some {x y : ℚ} (h : W.Nonsingular x y) :
    (Point.some x y h).weilHeight = logHeight₁ x :=
  rfl

namespace Point
p2m_open_scoped "WeierstrassCurve.Affine.Point" in
private lemma _root_.WeierstrassCurve.Affine.Point.weilHeight_nonneg (P : W.Point) : 0 ≤ P.weilHeight :=
  zero_le_logHeight₁ _

end Point
p2m_export "WeierstrassCurve.Affine" "Point.weilHeight_nonneg"

scoped instance instNorthcottWeilHeight : Northcott (Point.weilHeight (W := W)) :=
  ⟨fun b => Northcott.finite_le (h := logHeight₁ ∘ W.xCoord) b⟩

p2m_open_scoped "WeierstrassCurve.Affine.Point" in

theorem Point.finite_setOf_weilHeight_le (b : ℝ) : {P : W.Point | P.weilHeight ≤ b}.Finite :=
  Northcott.finite_le b

end Rat

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve"

set_option autoImplicit false

p2m_open "Height P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.Height Polynomial Real"

namespace Height
p2m_export "Height" "logHeight₁ mulHeight₁_pos logHeight_smul_eq_logHeight abs_logHeight_sym2_sub_le mulHeightBound logHeight_eval_ge zero_le_logHeight₁ AdmissibleAbsValues logHeight_eval_le logHeight₁_eq_logHeight mulHeight logHeight_eval_ge' logHeight logHeight₁_div_eq_logHeight logHeight₁_eq_log_mulHeight₁ mulHeight₁"
p2m_open "Height"

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

theorem logHeight_eval_le_of_natDegree_le {n : ℕ} {d : ℕ} (p : Fin n → K[X])
    (hp : ∀ j, (p j).natDegree ≤ d) :
    ∃ C : ℝ, ∀ x : K, logHeight (fun j => (p j).eval x) ≤ C + (d : ℝ) * logHeight₁ x := by
  refine ⟨log (max (mulHeightBound fun j => (p j).homogenize d) 1), fun x => ?_⟩
  have hx1 : (![x, 1] : Fin 2 → K) 1 ≠ 0 := by simp
  have key := logHeight_eval_le (p := fun j => (p j).homogenize d)
    (fun j => Polynomial.isHomogeneous_homogenize _) ![x, 1]
  have heval : ∀ j, MvPolynomial.eval ![x, 1] ((p j).homogenize d) = (p j).eval x := by
    intro j
    rw [Polynomial.eval_homogenize (hp j) _ hx1]
    simp
  simp only [heval] at key
  rwa [← logHeight₁_eq_logHeight] at key

theorem logHeight₁_eval_div_le {d : ℕ} (p q : K[X]) (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) :
    ∃ C : ℝ, ∀ x : K, logHeight₁ (p.eval x / q.eval x) ≤ C + (d : ℝ) * logHeight₁ x := by
  obtain ⟨C, hC⟩ := logHeight_eval_le_of_natDegree_le ![p, q] fun j => by fin_cases j <;> simpa
  refine ⟨C, fun x => ?_⟩
  rw [logHeight₁_div_eq_logHeight]
  have := hC x
  refine le_trans (le_of_eq ?_) this
  congr 1
  funext j
  fin_cases j <;> simp

theorem exists_logHeight₁_add_logHeight₁_le_logHeight_sym2 (K : Type*) [Field K]
    [AdmissibleAbsValues K] :
    ∃ C : ℝ, ∀ α β : K,
      logHeight₁ α + logHeight₁ β ≤ logHeight ![α * β, α + β, 1] + C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le K
  refine ⟨C, fun α β => ?_⟩
  have hα : (![α, 1] : Fin 2 → K) ≠ 0 := by simp
  have hβ : (![β, 1] : Fin 2 → K) ≠ 0 := by simp
  have key := (abs_le.mp (hC hα hβ)).1
  simp only [mul_one, one_mul] at key
  rw [logHeight₁_eq_logHeight, logHeight₁_eq_logHeight]
  linarith

end Height
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map b₂ Ψ₂Sq a₄ a₂ a₆ reduction Affine.Point b₆ b₈ Δ j b₄"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.eq_or_eq_neg_of_xRep_eq_xRep Equation negY slope_of_X_ne Point.xRep_some slope map Point.some Point.X_eq_iff Nonsingular Point.add_self_of_Y_eq Point.zero_def nonsingular_add slope_of_Y_ne Point addX nonsingular_neg Point.add_of_X_ne equation_iff polynomial Point.zero Point.neg_some Point.add_self_of_Y_ne"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

section Kummer

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x₁ x₂ y₁ y₂ : F}

lemma addX_slope_mul_sub_sq (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) + (-W.a₂ - x₁ - x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hL : (x₁ - x₂) * W.slope x₁ x₂ y₁ y₂ = y₁ - y₂ := by
    rw [slope_of_X_ne hx]
    field_simp
  simp only [addX]
  linear_combination
    ((x₁ - x₂) * W.slope x₁ x₂ y₁ y₂ + (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * hL

lemma addX_slope_negY_mul_sub_sq (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2 =
      (y₁ + y₂ + W.a₁ * x₂ + W.a₃) ^ 2 + W.a₁ * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * (x₁ - x₂)
        + (-W.a₂ - x₁ - x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hM : (x₁ - x₂) * W.slope x₁ x₂ y₁ (W.negY x₂ y₂) = y₁ + y₂ + W.a₁ * x₂ + W.a₃ := by
    rw [slope_of_X_ne hx, negY]
    field_simp
    ring
  simp only [addX]
  linear_combination
    ((x₁ - x₂) * W.slope x₁ x₂ y₁ (W.negY x₂ y₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃)
      + W.a₁ * (x₁ - x₂)) * hM

theorem addX_add_addX_negY_mul_sub_sq (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) + W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)))
        * (x₁ - x₂) ^ 2 =
      2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) + W.b₆ := by
  have e₁ := (W.equation_iff x₁ y₁).mp h₁
  have e₂ := (W.equation_iff x₂ y₂).mp h₂
  have hA := addX_slope_mul_sub_sq (W := W) (y₁ := y₁) (y₂ := y₂) hx
  have hB := addX_slope_negY_mul_sub_sq (W := W) (y₁ := y₁) (y₂ := y₂) hx
  simp only [b₂, b₄, b₆]
  linear_combination hA + hB + 2 * e₁ + 2 * e₂

theorem addX_mul_addX_negY_mul_sub_sq (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))
        * (x₁ - x₂) ^ 2 =
      x₁ ^ 2 * x₂ ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have e₁ := (W.equation_iff x₁ y₁).mp h₁
  have e₂ := (W.equation_iff x₂ y₂).mp h₂
  have hA := addX_slope_mul_sub_sq (W := W) (y₁ := y₁) (y₂ := y₂) hx
  have hB := addX_slope_negY_mul_sub_sq (W := W) (y₁ := y₁) (y₂ := y₂) hx

  have key : ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) + (-W.a₂ - x₁ - x₂) * (x₁ - x₂) ^ 2)
      * ((y₁ + y₂ + W.a₁ * x₂ + W.a₃) ^ 2 + W.a₁ * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * (x₁ - x₂)
        + (-W.a₂ - x₁ - x₂) * (x₁ - x₂) ^ 2) =
      (x₁ ^ 2 * x₂ ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := by
    simp only [b₄, b₆, b₈]
    linear_combination
      (y₁ ^ 2 - x₁ ^ 3 - 6 * x₂ ^ 3 - 3 * W.a₆ + 2 * y₂ ^ 2 + W.a₃ * y₁ + W.a₄ * x₁
        - W.a₂ * x₁ ^ 2 - W.a₁ ^ 2 * x₂ ^ 2 - 6 * W.a₂ * x₂ ^ 2 - 4 * W.a₄ * x₂
        + 2 * W.a₃ * y₂ + 2 * x₁ * x₂ ^ 2 + 2 * x₂ * x₁ ^ 2 + W.a₁ * W.a₃ * x₁
        + W.a₁ * x₁ * y₁ + x₁ * x₂ * W.a₁ ^ 2 - W.a₁ * W.a₃ * x₂ + 2 * W.a₁ * x₂ * y₂
        + 4 * W.a₂ * x₁ * x₂) * e₁
      + (y₂ ^ 2 - x₂ ^ 3 - 4 * y₁ ^ 2 + 3 * W.a₆ + W.a₃ * y₂ + W.a₄ * x₂ - W.a₂ * x₂ ^ 2
        - W.a₁ ^ 2 * x₁ ^ 2 - 4 * W.a₃ * y₁ + 2 * W.a₄ * x₁ + 2 * x₁ * x₂ ^ 2
        + 2 * x₂ * x₁ ^ 2 + W.a₁ * W.a₃ * x₂ + W.a₁ * x₂ * y₂ + x₁ * x₂ * W.a₁ ^ 2
        - W.a₁ * W.a₃ * x₁ - 4 * W.a₁ * x₁ * y₁ + 4 * W.a₂ * x₁ * x₂) * e₂
  refine mul_right_cancel₀ (pow_ne_zero 2 hd) ?_
  calc W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))
        * (x₁ - x₂) ^ 2 * (x₁ - x₂) ^ 2
      = (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2)
          * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2) := by ring
    _ = (x₁ ^ 2 * x₂ ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := by
          rw [hA, hB, key]

end Kummer
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

section Rat

variable {W : Affine ℚ}

theorem exists_logHeight₁_addX_add_logHeight₁_addX_negY_le {x₂ y₂ : ℚ}
    (h₂ : W.Equation x₂ y₂) :
    ∃ C : ℝ, ∀ ⦃x₁ y₁ : ℚ⦄, W.Equation x₁ y₁ → x₁ ≠ x₂ →
      logHeight₁ (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        + logHeight₁ (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)))
        ≤ 2 * logHeight₁ x₁ + C := by
  obtain ⟨Csym, hCsym⟩ := exists_logHeight₁_add_logHeight₁_le_logHeight_sym2 ℚ

  obtain ⟨Cpoly, hCpoly⟩ := logHeight_eval_le_of_natDegree_le (d := 2)
    ![C (x₂ ^ 2) * X ^ 2 + C (-(W.b₄ * x₂) - W.b₆) * X + C (-(W.b₆ * x₂) - W.b₈),
      C (2 * x₂) * X ^ 2 + C (2 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * X + C (W.b₄ * x₂ + W.b₆),
      C 1 * X ^ 2 + C (-(2 * x₂)) * X + C (x₂ ^ 2)]
    (by intro j; fin_cases j <;> exact natDegree_quadratic_le)
  refine ⟨Csym + Cpoly, fun x₁ y₁ h₁ hx => ?_⟩
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  set α := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) with hα
  set β := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) with hβ

  have step1 : logHeight₁ α + logHeight₁ β ≤ logHeight ![α * β, α + β, 1] + Csym := hCsym α β

  have step2 : logHeight (![α * β, α + β, 1] : Fin 3 → ℚ) =
      logHeight ![α * β * (x₁ - x₂) ^ 2, (α + β) * (x₁ - x₂) ^ 2, (x₁ - x₂) ^ 2] := by
    rw [show (![α * β * (x₁ - x₂) ^ 2, (α + β) * (x₁ - x₂) ^ 2, (x₁ - x₂) ^ 2] : Fin 3 → ℚ)
          = (x₁ - x₂) ^ 2 • ![α * β, α + β, 1] by
        funext j
        fin_cases j <;> simp [mul_comm]]
    rw [logHeight_smul_eq_logHeight _ (pow_ne_zero 2 hd)]
  have id₂ := addX_add_addX_negY_mul_sub_sq h₁ h₂ hx
  have id₃ := addX_mul_addX_negY_mul_sub_sq h₁ h₂ hx
  have step3 : (![α * β * (x₁ - x₂) ^ 2, (α + β) * (x₁ - x₂) ^ 2, (x₁ - x₂) ^ 2] : Fin 3 → ℚ)
      = fun j =>
        (![C (x₂ ^ 2) * X ^ 2 + C (-(W.b₄ * x₂) - W.b₆) * X + C (-(W.b₆ * x₂) - W.b₈),
           C (2 * x₂) * X ^ 2 + C (2 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * X + C (W.b₄ * x₂ + W.b₆),
           C 1 * X ^ 2 + C (-(2 * x₂)) * X + C (x₂ ^ 2)] j).eval x₁ := by
    rw [← hα, ← hβ] at id₂ id₃
    funext j
    fin_cases j
    · show α * β * (x₁ - x₂) ^ 2
        = (C (x₂ ^ 2) * X ^ 2 + C (-(W.b₄ * x₂) - W.b₆) * X + C (-(W.b₆ * x₂) - W.b₈)).eval x₁
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination id₃
    · show (α + β) * (x₁ - x₂) ^ 2
        = (C (2 * x₂) * X ^ 2 + C (2 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * X
            + C (W.b₄ * x₂ + W.b₆)).eval x₁
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination id₂
    · show (x₁ - x₂) ^ 2 = (C 1 * X ^ 2 + C (-(2 * x₂)) * X + C (x₂ ^ 2)).eval x₁
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring

  have step4 := hCpoly x₁
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at step4
  calc logHeight₁ α + logHeight₁ β
      ≤ logHeight ![α * β, α + β, 1] + Csym := step1
    _ = logHeight (fun j =>
          (![C (x₂ ^ 2) * X ^ 2 + C (-(W.b₄ * x₂) - W.b₆) * X + C (-(W.b₆ * x₂) - W.b₈),
             C (2 * x₂) * X ^ 2 + C (2 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * X + C (W.b₄ * x₂ + W.b₆),
             C 1 * X ^ 2 + C (-(2 * x₂)) * X + C (x₂ ^ 2)] j).eval x₁) + Csym := by
        rw [step2, step3]
    _ ≤ Cpoly + 2 * logHeight₁ x₁ + Csym := by linarith
    _ = 2 * logHeight₁ x₁ + (Csym + Cpoly) := by ring

namespace Point
p2m_open_scoped "WeierstrassCurve.Affine.Point" in

private theorem _root_.WeierstrassCurve.Affine.Point.exists_weilHeight_add_add_weilHeight_sub_le (P : W.Point) :
    ∃ c : ℝ, ∀ R : W.Point, (R + P).weilHeight + (R - P).weilHeight ≤ 2 * R.weilHeight + c := by
  rcases P with _ | ⟨x₂, y₂, h₂⟩
  ·
    refine ⟨0, fun R => ?_⟩
    rw [← Point.zero_def, add_zero, sub_zero]
    linarith
  · obtain ⟨Cgen, hCgen⟩ := exists_logHeight₁_addX_add_logHeight₁_addX_negY_le (W := W) h₂.left
    set Q : W.Point := Point.some x₂ y₂ h₂ with hQdef

    set cSpec : ℝ :=
      ((0 : W.Point) + Q).weilHeight + ((0 : W.Point) - Q).weilHeight
        + (Q + Q).weilHeight + (Q - Q).weilHeight
        + (-Q + Q).weilHeight + (-Q - Q).weilHeight with hcSpec
    have hcSpec₁ : ((0 : W.Point) + Q).weilHeight + ((0 : W.Point) - Q).weilHeight ≤ cSpec := by
      have := (Q + Q).weilHeight_nonneg
      have := (Q - Q).weilHeight_nonneg
      have := (-Q + Q).weilHeight_nonneg
      have := (-Q - Q).weilHeight_nonneg
      rw [hcSpec]; linarith
    have hcSpec₂ : (Q + Q).weilHeight + (Q - Q).weilHeight ≤ cSpec := by
      have := ((0 : W.Point) + Q).weilHeight_nonneg
      have := ((0 : W.Point) - Q).weilHeight_nonneg
      have := (-Q + Q).weilHeight_nonneg
      have := (-Q - Q).weilHeight_nonneg
      rw [hcSpec]; linarith
    have hcSpec₃ : (-Q + Q).weilHeight + (-Q - Q).weilHeight ≤ cSpec := by
      have := ((0 : W.Point) + Q).weilHeight_nonneg
      have := ((0 : W.Point) - Q).weilHeight_nonneg
      have := (Q + Q).weilHeight_nonneg
      have := (Q - Q).weilHeight_nonneg
      rw [hcSpec]; linarith
    refine ⟨max Cgen cSpec, fun R => ?_⟩
    rcases R with _ | ⟨x₁, y₁, h₁⟩
    ·
      rw [← Point.zero_def]
      exact le_trans (hcSpec₁.trans (le_max_right _ _))
        (le_add_of_nonneg_left (mul_nonneg (by norm_num) (Point.weilHeight_nonneg _)))
    · by_cases hx : x₁ = x₂
      ·
        rcases Point.X_eq_iff.mp hx with hRQ | hRQ
        · rw [hRQ, ← hQdef]
          exact le_trans (hcSpec₂.trans (le_max_right _ _))
            (le_add_of_nonneg_left (mul_nonneg (by norm_num) (Point.weilHeight_nonneg _)))
        · rw [hRQ, ← hQdef]
          exact le_trans (hcSpec₃.trans (le_max_right _ _))
            (le_add_of_nonneg_left (mul_nonneg (by norm_num) (Point.weilHeight_nonneg _)))
      ·
        have key := hCgen h₁.left hx
        have hadd : Point.some x₁ y₁ h₁ + Q
            = Point.some _ _ (nonsingular_add h₁ h₂ fun hxy => hx hxy.left) :=
          Point.add_of_X_ne hx
        have hsub : Point.some x₁ y₁ h₁ - Q
            = Point.some _ _
                (nonsingular_add h₁ ((nonsingular_neg ..).mpr h₂) fun hxy => hx hxy.left) := by
          rw [sub_eq_add_neg, hQdef, Point.neg_some]
          exact Point.add_of_X_ne hx
        rw [hadd, hsub, Point.weilHeight_some, Point.weilHeight_some, Point.weilHeight_some]
        exact le_trans (by exact key) (by have := le_max_left Cgen cSpec; linarith)

end Point
p2m_export "WeierstrassCurve.Affine" "Point.exists_weilHeight_add_add_weilHeight_sub_le"

def HeightTranslationBound (W : Affine ℚ) : Prop :=
  ∃ c : W.Point → ℝ, ∀ g x : W.Point, x.weilHeight ≤ 2 * (g + x).weilHeight + c g

def HeightDuplicationBound (W : Affine ℚ) : Prop :=
  ∃ c₀ : ℝ, ∀ x : W.Point, 4 * x.weilHeight - c₀ ≤ (2 • x).weilHeight

theorem heightTranslationBound (W : Affine ℚ) : HeightTranslationBound W := by
  choose c hc using fun P : W.Point => P.exists_weilHeight_add_add_weilHeight_sub_le
  refine ⟨c, fun g x => ?_⟩

  have key := hc g (g + x)
  rw [add_sub_cancel_left] at key
  have := (g + x + g).weilHeight_nonneg
  linarith

p2m_open_scoped "WeierstrassCurve.Affine.Point" in

theorem Point.addGroup_fg (W : Affine ℚ)
    (hweak : (nsmulAddMonoidHom 2 : W.Point →+ W.Point).range.FiniteIndex)
    (hdupl : HeightDuplicationBound W) :
    AddGroup.FG W.Point := by
  obtain ⟨c, hc⟩ := heightTranslationBound W
  obtain ⟨c₀, hc₀⟩ := hdupl
  exact AddCommGroup.fg_of_descent (n := 2) (h := Point.weilHeight) (a := 2) (b := 4) (c := c)
    (c₀ := c₀) (by norm_num) (by norm_num) hweak hc hc₀

end Rat
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

set_option autoImplicit false

p2m_open "Height P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.Height Polynomial Real.Polynomial Real"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map b₂ Ψ₂Sq a₄ a₂ a₆ reduction Affine.Point b₆ b₈ Δ j b₄"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.eq_or_eq_neg_of_xRep_eq_xRep Equation negY slope_of_X_ne Point.xRep_some slope map Point.some Point.X_eq_iff Nonsingular Point.add_self_of_Y_eq Point.zero_def nonsingular_add slope_of_Y_ne Point addX nonsingular_neg Point.add_of_X_ne equation_iff polynomial Point.zero Point.neg_some Point.add_self_of_Y_ne"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

section Certificate

variable {R : Type*} [CommRing R]

private noncomputable def dupPhi (B₄ B₆ B₈ : R) : R[X] :=
  X ^ 4 - C B₄ * X ^ 2 - C (2 * B₆) * X - C B₈

private noncomputable def dupPsi (B₂ B₄ B₆ : R) : R[X] :=
  C 4 * X ^ 3 + C B₂ * X ^ 2 + C (2 * B₄) * X + C B₆

private def dupRes (B₂ B₄ B₆ B₈ : R) : R :=
  B₂ ^ 4 * B₈ ^ 2 - 6 * B₂ ^ 3 * B₄ * B₆ * B₈ + 4 * B₂ ^ 3 * B₆ ^ 3 + 4 * B₂ ^ 2 * B₄ ^ 3 * B₈
    - 3 * B₂ ^ 2 * B₄ ^ 2 * B₆ ^ 2 - 48 * B₂ ^ 2 * B₄ * B₈ ^ 2 + 6 * B₂ ^ 2 * B₆ ^ 2 * B₈
    + 240 * B₂ * B₄ ^ 2 * B₆ * B₈ - 162 * B₂ * B₄ * B₆ ^ 3 + 192 * B₂ * B₆ * B₈ ^ 2
    - 144 * B₄ ^ 4 * B₈ + 108 * B₄ ^ 3 * B₆ ^ 2 + 384 * B₄ ^ 2 * B₈ ^ 2 - 1296 * B₄ * B₆ ^ 2 * B₈
    + 729 * B₆ ^ 4 - 256 * B₈ ^ 3

private noncomputable def dupCofXPhi (B₂ B₄ B₆ B₈ : R) : R[X] :=
  C (B₂ ^ 4 * B₈ ^ 2 - 6 * B₂ ^ 3 * B₄ * B₆ * B₈ + 4 * B₂ ^ 3 * B₆ ^ 3 + 4 * B₂ ^ 2 * B₄ ^ 3 * B₈
      - 3 * B₂ ^ 2 * B₄ ^ 2 * B₆ ^ 2 - 48 * B₂ ^ 2 * B₄ * B₈ ^ 2 + 6 * B₂ ^ 2 * B₆ ^ 2 * B₈
      + 240 * B₂ * B₄ ^ 2 * B₆ * B₈ - 162 * B₂ * B₄ * B₆ ^ 3 + 192 * B₂ * B₆ * B₈ ^ 2
      - 144 * B₄ ^ 4 * B₈ + 108 * B₄ ^ 3 * B₆ ^ 2 + 384 * B₄ ^ 2 * B₈ ^ 2
      - 1296 * B₄ * B₆ ^ 2 * B₈ + 729 * B₆ ^ 4 - 256 * B₈ ^ 3) * X ^ 3
    + C (-4 * B₂ ^ 3 * B₄ * B₈ ^ 2 + 24 * B₂ ^ 2 * B₄ ^ 2 * B₆ * B₈ - 16 * B₂ ^ 2 * B₄ * B₆ ^ 3
      + 36 * B₂ ^ 2 * B₆ * B₈ ^ 2 - 16 * B₂ * B₄ ^ 4 * B₈ + 12 * B₂ * B₄ ^ 3 * B₆ ^ 2
      + 48 * B₂ * B₄ ^ 2 * B₈ ^ 2 - 240 * B₂ * B₄ * B₆ ^ 2 * B₈ + 144 * B₂ * B₆ ^ 4
      - 64 * B₂ * B₈ ^ 3 + 48 * B₄ ^ 3 * B₆ * B₈ - 36 * B₄ ^ 2 * B₆ ^ 3 + 64 * B₄ * B₆ * B₈ ^ 2
      - 36 * B₆ ^ 3 * B₈) * X ^ 2
    + C (B₂ ^ 3 * B₆ * B₈ ^ 2 - 12 * B₂ ^ 2 * B₄ ^ 2 * B₈ ^ 2 - 6 * B₂ ^ 2 * B₄ * B₆ ^ 2 * B₈
      + 4 * B₂ ^ 2 * B₆ ^ 4 + 76 * B₂ * B₄ ^ 3 * B₆ * B₈ - 51 * B₂ * B₄ ^ 2 * B₆ ^ 3
      + 64 * B₂ * B₄ * B₆ * B₈ ^ 2 + 7 * B₂ * B₆ ^ 3 * B₈ - 48 * B₄ ^ 5 * B₈
      + 36 * B₄ ^ 4 * B₆ ^ 2 + 160 * B₄ ^ 3 * B₈ ^ 2 - 528 * B₄ ^ 2 * B₆ ^ 2 * B₈
      + 297 * B₄ * B₆ ^ 4 - 128 * B₄ * B₈ ^ 3 + 16 * B₆ ^ 2 * B₈ ^ 2) * X
    + C (-6 * B₂ ^ 2 * B₄ * B₆ * B₈ ^ 2 + 36 * B₂ * B₄ ^ 2 * B₆ ^ 2 * B₈ - 24 * B₂ * B₄ * B₆ ^ 4
      + 40 * B₂ * B₆ ^ 2 * B₈ ^ 2 - 24 * B₄ ^ 4 * B₆ * B₈ + 18 * B₄ ^ 3 * B₆ ^ 3
      + 80 * B₄ ^ 2 * B₆ * B₈ ^ 2 - 282 * B₄ * B₆ ^ 3 * B₈ + 162 * B₆ ^ 5 - 64 * B₆ * B₈ ^ 3)

private noncomputable def dupCofXPsi (B₂ B₄ B₆ B₈ : R) : R[X] :=
  C (B₂ ^ 3 * B₄ * B₈ ^ 2 - 6 * B₂ ^ 2 * B₄ ^ 2 * B₆ * B₈ + 4 * B₂ ^ 2 * B₄ * B₆ ^ 3
      - 9 * B₂ ^ 2 * B₆ * B₈ ^ 2 + 4 * B₂ * B₄ ^ 4 * B₈ - 3 * B₂ * B₄ ^ 3 * B₆ ^ 2
      - 12 * B₂ * B₄ ^ 2 * B₈ ^ 2 + 60 * B₂ * B₄ * B₆ ^ 2 * B₈ - 36 * B₂ * B₆ ^ 4
      + 16 * B₂ * B₈ ^ 3 - 12 * B₄ ^ 3 * B₆ * B₈ + 9 * B₄ ^ 2 * B₆ ^ 3 - 16 * B₄ * B₆ * B₈ ^ 2
      + 9 * B₆ ^ 3 * B₈) * X ^ 3
    + C (2 * B₂ ^ 3 * B₆ * B₈ ^ 2 - 6 * B₂ ^ 2 * B₄ ^ 2 * B₈ ^ 2 - 12 * B₂ ^ 2 * B₄ * B₆ ^ 2 * B₈
      + 8 * B₂ ^ 2 * B₆ ^ 4 - 4 * B₂ ^ 2 * B₈ ^ 3 + 44 * B₂ * B₄ ^ 3 * B₆ * B₈
      - 30 * B₂ * B₄ ^ 2 * B₆ ^ 3 + 36 * B₂ * B₄ * B₆ * B₈ ^ 2 - 4 * B₂ * B₆ ^ 3 * B₈
      - 24 * B₄ ^ 5 * B₈ + 18 * B₄ ^ 4 * B₆ ^ 2 + 56 * B₄ ^ 3 * B₈ ^ 2
      - 192 * B₄ ^ 2 * B₆ ^ 2 * B₈ + 108 * B₄ * B₆ ^ 4 - 32 * B₄ * B₈ ^ 3
      - 4 * B₆ ^ 2 * B₈ ^ 2) * X ^ 2
    + C (B₂ ^ 3 * B₈ ^ 3 - 18 * B₂ ^ 2 * B₄ * B₆ * B₈ ^ 2 + 4 * B₂ ^ 2 * B₆ ^ 3 * B₈
      + 4 * B₂ * B₄ ^ 3 * B₈ ^ 2 + 69 * B₂ * B₄ ^ 2 * B₆ ^ 2 * B₈ - 48 * B₂ * B₄ * B₆ ^ 4
      - 16 * B₂ * B₄ * B₈ ^ 3 + 87 * B₂ * B₆ ^ 2 * B₈ ^ 2 - 48 * B₄ ^ 4 * B₆ * B₈
      + 36 * B₄ ^ 3 * B₆ ^ 3 + 196 * B₄ ^ 2 * B₆ * B₈ ^ 2 - 591 * B₄ * B₆ ^ 3 * B₈
      + 324 * B₆ ^ 5 - 112 * B₆ * B₈ ^ 3) * X
    + C (-6 * B₂ ^ 2 * B₄ * B₈ ^ 3 + 36 * B₂ * B₄ ^ 2 * B₆ * B₈ ^ 2 - 24 * B₂ * B₄ * B₆ ^ 3 * B₈
      + 40 * B₂ * B₆ * B₈ ^ 3 - 24 * B₄ ^ 4 * B₈ ^ 2 + 18 * B₄ ^ 3 * B₆ ^ 2 * B₈
      + 80 * B₄ ^ 2 * B₈ ^ 3 - 282 * B₄ * B₆ ^ 2 * B₈ ^ 2 + 162 * B₆ ^ 4 * B₈ - 64 * B₈ ^ 4)

private noncomputable def dupCofZPhi (B₂ B₄ B₆ B₈ : R) : R[X] :=
  C (8 * B₂ ^ 3 * B₆ - 8 * B₂ ^ 2 * B₄ ^ 2 + 16 * B₂ ^ 2 * B₈ - 336 * B₂ * B₄ * B₆
      + 288 * B₄ ^ 3 - 384 * B₄ * B₈ + 1296 * B₆ ^ 2) * X ^ 2
    + C (2 * B₂ ^ 4 * B₆ - 2 * B₂ ^ 3 * B₄ ^ 2 - 80 * B₂ ^ 2 * B₄ * B₆ + 72 * B₂ * B₄ ^ 3
      + 32 * B₂ * B₄ * B₈ + 360 * B₂ * B₆ ^ 2 - 144 * B₄ ^ 2 * B₆ - 576 * B₆ * B₈) * X
    + C (-B₂ ^ 4 * B₈ + 5 * B₂ ^ 3 * B₄ * B₆ - 4 * B₂ ^ 2 * B₄ ^ 3 + 48 * B₂ ^ 2 * B₄ * B₈
      + B₂ ^ 2 * B₆ ^ 2 - 204 * B₂ * B₄ ^ 2 * B₆ - 176 * B₂ * B₆ * B₈ + 144 * B₄ ^ 4
      - 384 * B₄ ^ 2 * B₈ + 864 * B₄ * B₆ ^ 2 + 256 * B₈ ^ 2)

private noncomputable def dupCofZPsi (B₂ B₄ B₆ B₈ : R) : R[X] :=
  C (-2 * B₂ ^ 3 * B₆ + 2 * B₂ ^ 2 * B₄ ^ 2 - 4 * B₂ ^ 2 * B₈ + 84 * B₂ * B₄ * B₆
      - 72 * B₄ ^ 3 + 96 * B₄ * B₈ - 324 * B₆ ^ 2) * X ^ 3
    + C (B₂ ^ 3 * B₈ - B₂ ^ 2 * B₄ * B₆ - 32 * B₂ * B₄ * B₈ - 9 * B₂ * B₆ ^ 2
      + 36 * B₄ ^ 2 * B₆ + 144 * B₆ * B₈) * X ^ 2
    + C (2 * B₂ ^ 3 * B₄ * B₆ - 2 * B₂ ^ 2 * B₄ ^ 3 + 2 * B₂ ^ 2 * B₄ * B₈ + 2 * B₂ ^ 2 * B₆ ^ 2
      - 84 * B₂ * B₄ ^ 2 * B₆ + 8 * B₂ * B₆ * B₈ + 72 * B₄ ^ 4 - 48 * B₄ ^ 2 * B₈
      + 270 * B₄ * B₆ ^ 2 - 64 * B₈ ^ 2) * X
    + C (-B₂ ^ 3 * B₄ * B₈ + 4 * B₂ ^ 3 * B₆ ^ 2 - 3 * B₂ ^ 2 * B₄ ^ 2 * B₆ + 7 * B₂ ^ 2 * B₆ * B₈
      + 36 * B₂ * B₄ ^ 2 * B₈ - 162 * B₂ * B₄ * B₆ ^ 2 + 16 * B₂ * B₈ ^ 2 + 108 * B₄ ^ 3 * B₆
      - 432 * B₄ * B₆ * B₈ + 729 * B₆ ^ 3)

private lemma natDegree_dupPhi_le (B₄ B₆ B₈ : R) : (dupPhi B₄ B₆ B₈).natDegree ≤ 4 := by
  unfold dupPhi; compute_degree

private lemma natDegree_dupPsi_le (B₂ B₄ B₆ : R) : (dupPsi B₂ B₄ B₆).natDegree ≤ 4 :=
  natDegree_cubic_le.trans (by norm_num)

private lemma natDegree_dupCofXPhi_le (B₂ B₄ B₆ B₈ : R) :
    (dupCofXPhi B₂ B₄ B₆ B₈).natDegree ≤ 3 :=
  natDegree_cubic_le

private lemma natDegree_dupCofXPsi_le (B₂ B₄ B₆ B₈ : R) :
    (dupCofXPsi B₂ B₄ B₆ B₈).natDegree ≤ 3 :=
  natDegree_cubic_le

private lemma natDegree_dupCofZPhi_le (B₂ B₄ B₆ B₈ : R) :
    (dupCofZPhi B₂ B₄ B₆ B₈).natDegree ≤ 3 :=
  natDegree_quadratic_le.trans (by norm_num)

private lemma natDegree_dupCofZPsi_le (B₂ B₄ B₆ B₈ : R) :
    (dupCofZPsi B₂ B₄ B₆ B₈).natDegree ≤ 3 :=
  natDegree_cubic_le

private lemma dup_cert_one (B₂ B₄ B₆ B₈ t : R) :
    (dupCofZPhi B₂ B₄ B₆ B₈).eval t * (dupPhi B₄ B₆ B₈).eval t
      + (dupCofZPsi B₂ B₄ B₆ B₈).eval t * (dupPsi B₂ B₄ B₆).eval t
      = dupRes B₂ B₄ B₆ B₈ := by
  simp only [dupCofZPhi, dupCofZPsi, dupPhi, dupPsi, dupRes, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X]
  ring

set_option maxHeartbeats 6400000 in

private lemma dup_cert_X (B₂ B₄ B₆ B₈ t : R) :
    (dupCofXPhi B₂ B₄ B₆ B₈).eval t * (dupPhi B₄ B₆ B₈).eval t
      + (dupCofXPsi B₂ B₄ B₆ B₈).eval t * (dupPsi B₂ B₄ B₆).eval t
      = dupRes B₂ B₄ B₆ B₈ * t ^ 7 := by
  simp only [dupCofXPhi, dupCofXPsi, dupPhi, dupPsi, dupRes, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X]
  ring

private lemma dupRes_eq_Δ_sq (W : WeierstrassCurve R) :
    dupRes W.b₂ W.b₄ W.b₆ W.b₈ = W.Δ ^ 2 := by
  simp only [dupRes, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, WeierstrassCurve.Δ]
  ring

end Certificate
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

section DuplicationFormula

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

omit [DecidableEq F] in

private lemma sq_sub_negY (h : W.Equation x y) :
    (y - W.negY x y) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [negY, b₂, b₄, b₆]
  linear_combination 4 * (W.equation_iff x y).mp h

omit [DecidableEq F] in

lemma sub_negY_eq_zero_iff (h : W.Equation x y) :
    y = W.negY x y ↔ 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
  rw [← sq_sub_negY h, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem addX_self_mul (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have hD : y - W.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hN : W.slope x x y y * (y - W.negY x y)
      = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy]
    field_simp
  rw [← sq_sub_negY h]
  simp only [addX, negY, b₄, b₆, b₈] at hN ⊢
  linear_combination
    (W.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
      + W.a₁ * (y - (-y - W.a₁ * x - W.a₃))) * hN
    + (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x) * ((W.equation_iff x y).mp h)

theorem addX_self_eq_div (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y)
      = (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)
        / (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 :=
    fun h0 => hy ((sub_negY_eq_zero_iff h).mpr h0)
  rw [eq_div_iff hψ, addX_self_mul h hy]

end DuplicationFormula
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

section TwoTorsion

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

p2m_open_scoped "WeierstrassCurve.Affine.Point" in

theorem Point.finite_setOf_add_self_eq_zero [CharZero F] :
    {P : W.Point | P + P = 0}.Finite := by
  classical

  have hψ : (C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : F[X]) ≠ 0 := by
    intro h0
    have h3 : (C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : F[X]).natDegree = 3 :=
      natDegree_cubic (by norm_num)
    rw [h0, natDegree_zero] at h3
    exact absurd h3 (by norm_num)
  refine Set.Finite.subset (Set.Finite.insert 0
    ((finite_setOf_isRoot hψ).biUnion fun c _ => finite_preimage_xCoord c)) fun P hP => ?_
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ (Set.mem_biUnion ?_ (show _ ∈ W.xCoord ⁻¹' {x} from rfl))

    have hy : y = W.negY x y := by
      by_contra hy
      exact some_ne_zero (nonsingular_add h h fun hxy => hy hxy.right)
        (by simpa only [Set.mem_setOf_eq, add_self_of_Y_ne hy] using hP)
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    exact (sub_negY_eq_zero_iff h.left).mp hy

end TwoTorsion
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

section Rat

variable {W : Affine ℚ}

private theorem exists_le_logHeight₁_dup (hΔ : W.Δ ≠ 0) :
    ∃ c : ℝ, ∀ t : ℚ,
      c + 4 * logHeight₁ t ≤
        logHeight₁ ((t ^ 4 - W.b₄ * t ^ 2 - 2 * W.b₆ * t - W.b₈)
          / (4 * t ^ 3 + W.b₂ * t ^ 2 + 2 * W.b₄ * t + W.b₆)) := by
  have hΔ2 : (W.Δ : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hΔ

  obtain ⟨c, hc⟩ := logHeight_eval_ge' (K := ℚ) (ι := Fin 2) (ι' := Fin 2) (M := 3) (N := 4)
    (q := fun a =>
      (Polynomial.C (W.Δ ^ 2)⁻¹ *
        ![![dupCofXPhi W.b₂ W.b₄ W.b₆ W.b₈, dupCofXPsi W.b₂ W.b₄ W.b₆ W.b₈],
          ![dupCofZPhi W.b₂ W.b₄ W.b₆ W.b₈, dupCofZPsi W.b₂ W.b₄ W.b₆ W.b₈]] a.1 a.2).homogenize
        3)
    (fun _ => Polynomial.isHomogeneous_homogenize _)
  refine ⟨c, fun t => ?_⟩
  have h1 : (![t, 1] : Fin 2 → ℚ) 1 ≠ 0 := by simp

  have heval : ∀ (r : ℚ[X]) (n : ℕ), r.natDegree ≤ n →
      MvPolynomial.eval ![t, 1] (r.homogenize n) = r.eval t := by
    intro r n hr
    rw [Polynomial.eval_homogenize hr _ h1]
    simp

  have key := hc (p := ![(dupPhi W.b₄ W.b₆ W.b₈).homogenize 4,
      (dupPsi W.b₂ W.b₄ W.b₆).homogenize 4]) (x := ![t, 1]) ?hcert
  case hcert =>
    rw [Fin.forall_fin_two]
    constructor <;> rw [Fin.sum_univ_two] <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ·

      rw [heval _ _ ((natDegree_C_mul_le _ _).trans (natDegree_dupCofXPhi_le _ _ _ _)),
        heval _ _ ((natDegree_C_mul_le _ _).trans (natDegree_dupCofXPsi_le _ _ _ _)),
        heval _ _ (natDegree_dupPhi_le _ _ _), heval _ _ (natDegree_dupPsi_le _ _ _),
        eval_mul, eval_mul, eval_C]
      have cert := dup_cert_X W.b₂ W.b₄ W.b₆ W.b₈ t
      rw [dupRes_eq_Δ_sq] at cert
      field_simp
      linear_combination cert
    ·

      rw [heval _ _ ((natDegree_C_mul_le _ _).trans (natDegree_dupCofZPhi_le _ _ _ _)),
        heval _ _ ((natDegree_C_mul_le _ _).trans (natDegree_dupCofZPsi_le _ _ _ _)),
        heval _ _ (natDegree_dupPhi_le _ _ _), heval _ _ (natDegree_dupPsi_le _ _ _),
        eval_mul, eval_mul, eval_C]
      have cert := dup_cert_one W.b₂ W.b₄ W.b₆ W.b₈ t
      rw [dupRes_eq_Δ_sq] at cert
      field_simp
      linear_combination cert

  refine le_trans (le_of_eq ?_) (le_trans key (le_of_eq ?_))
  · rw [← logHeight₁_eq_logHeight t]
    norm_num
  · rw [logHeight₁_div_eq_logHeight]
    congr 1
    funext j
    fin_cases j
    · show MvPolynomial.eval ![t, 1] ((dupPhi W.b₄ W.b₆ W.b₈).homogenize 4)
        = t ^ 4 - W.b₄ * t ^ 2 - 2 * W.b₆ * t - W.b₈
      rw [heval _ _ (natDegree_dupPhi_le _ _ _)]
      simp only [dupPhi, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    · show MvPolynomial.eval ![t, 1] ((dupPsi W.b₂ W.b₄ W.b₆).homogenize 4)
        = 4 * t ^ 3 + W.b₂ * t ^ 2 + 2 * W.b₄ * t + W.b₆
      rw [heval _ _ (natDegree_dupPsi_le _ _ _)]
      simp only [dupPsi, eval_add, eval_mul, eval_pow, eval_C, eval_X]

theorem heightDuplicationBound_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : HeightDuplicationBound W := by
  classical

  obtain ⟨c, hc⟩ := exists_le_logHeight₁_dup hΔ

  obtain ⟨c₂, hc₂⟩ := ((Point.finite_setOf_add_self_eq_zero (W := W)).image
    fun P => 4 * P.weilHeight).bddAbove
  refine ⟨max (-c) c₂, fun P => ?_⟩
  rw [two_nsmul]
  by_cases hP : P + P = 0
  ·
    rw [hP]
    have : 4 * P.weilHeight ≤ c₂ := hc₂ ⟨P, hP, rfl⟩
    have h0 : (0 : W.Point).weilHeight = 0 := Point.weilHeight_zero
    rw [h0]
    have := le_max_right (-c) c₂
    linarith
  ·
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP
    have hy : y ≠ W.negY x y := fun hy => hP (Point.add_self_of_Y_eq hy)
    rw [Point.add_self_of_Y_ne hy, Point.weilHeight_some, Point.weilHeight_some,
      addX_self_eq_div h.left hy]
    have := hc x
    have := le_max_left (-c) c₂
    linarith

p2m_open_scoped "WeierstrassCurve.Affine.Point" in

theorem Point.addGroup_fg_of_Δ_ne_zero (hΔ : W.Δ ≠ 0)
    (hweak : (nsmulAddMonoidHom 2 : W.Point →+ W.Point).range.FiniteIndex) :
    AddGroup.FG W.Point :=
  Point.addGroup_fg W hweak (heightDuplicationBound_of_Δ_ne_zero hΔ)

end Rat
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex.WeierstrassCurve.Affine"

theorem solution (W : WeierstrassCurve.Affine ℚ) (hΔ : W.Δ ≠ 0) (hweak : (nsmulAddMonoidHom 2 : W.Point →+ W.Point).range.FiniteIndex) : AddGroup.FG W.Point := WeierstrassCurve.Affine.Point.addGroup_fg_of_Δ_ne_zero hΔ hweak

end S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_addGroup_fg_of_finiteIndex (solution)
