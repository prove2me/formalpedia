-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.finite_and_ncard_torsion_le_of_isNode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b3efc4e8-1396-5356-ad31-2471535b163f

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace NodalTorsion

section defs

variable {K : Type*} {W : WeierstrassCurve K}

private lemma e₁ : W.toAffine.a₁ = W.a₁ := rfl
private lemma e₂ : W.toAffine.a₂ = W.a₂ := rfl
private lemma e₃ : W.toAffine.a₃ = W.a₃ := rfl
private lemma e₄ : W.toAffine.a₄ = W.a₄ := rfl
private lemma e₆ : W.toAffine.a₆ = W.a₆ := rfl

end defs

variable {K : Type*} [Field K] {W : WeierstrassCurve K} {x₀ y₀ α : K}

structure Frame (W : WeierstrassCurve K) (x₀ y₀ α : K) : Prop where
  he : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) = 0
  hFX : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0
  hFY : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0
  hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0

noncomputable def tc (W : WeierstrassCurve K) (x₀ y₀ α : K) : W.toAffine.Point → K
  | .zero => 1
  | .some x y _ => (y - y₀ - α * (x - x₀)) / (y - y₀ - (-W.a₁ - α) * (x - x₀))

@[scoped simp] lemma tc_zero : tc W x₀ y₀ α 0 = 1 := rfl

@[scoped simp] lemma tc_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    tc W x₀ y₀ α (.some x y h) = (y - y₀ - α * (x - x₀)) / (y - y₀ - (-W.a₁ - α) * (x - x₀)) := rfl

variable (hd : Frame W x₀ y₀ α)
include hd

lemma factor_eq {x y : K} (h : W.toAffine.Equation x y) :
    (y - y₀ - α * (x - x₀)) * (y - y₀ - (-W.a₁ - α) * (x - x₀)) = (x - x₀) ^ 3 := by
  rw [equation_iff, e₁, e₂, e₃, e₄, e₆] at h
  linear_combination h - hd.he - (x - x₀) * hd.hFX - (y - y₀) * hd.hFY - (x - x₀) ^ 2 * hd.hα

lemma not_nonsingular_centre : ¬ W.toAffine.Nonsingular x₀ y₀ := by
  rw [nonsingular_iff', e₁, e₂, e₃, e₄]
  rintro ⟨-, h | h⟩
  · exact h hd.hFX
  · exact h hd.hFY

lemma factors_ne_zero {x y : K} (h : W.toAffine.Nonsingular x y) :
    y - y₀ - α * (x - x₀) ≠ 0 ∧ y - y₀ - (-W.a₁ - α) * (x - x₀) ≠ 0 := by
  have hfac := factor_eq hd h.left

  have hx0 : ∀ {u v : K}, u * v = (x - x₀) ^ 3 → u = 0 → x = x₀ := by
    intro u v huv hu
    rw [hu, zero_mul] at huv
    exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 3) (by norm_num)).mp huv.symm)
  constructor
  · intro hu
    have hx := hx0 hfac hu
    have hy : y = y₀ := by rw [hx, sub_self, mul_zero, sub_zero, sub_eq_zero] at hu; exact hu
    subst hx; subst hy
    exact not_nonsingular_centre hd h
  · intro hu
    rw [mul_comm] at hfac
    have hx := hx0 hfac hu
    have hy : y = y₀ := by rw [hx, sub_self, mul_zero, sub_zero, sub_eq_zero] at hu; exact hu
    subst hx; subst hy
    exact not_nonsingular_centre hd h

lemma tc_ne_zero (P : W.toAffine.Point) : tc W x₀ y₀ α P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact one_ne_zero
  · obtain ⟨h1, h2⟩ := factors_ne_zero hd h
    exact div_ne_zero h1 h2

lemma eq_zero_of_tc_eq_one (hαβ : α ≠ -W.a₁ - α) (P : W.toAffine.Point)
    (hP : tc W x₀ y₀ α P = 1) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · exfalso
    obtain ⟨h1, h2⟩ := factors_ne_zero hd h
    rw [tc_some, div_eq_one_iff_eq h2] at hP
    have hx : x = x₀ := by
      have : (α - (-W.a₁ - α)) * (x - x₀) = 0 := by linear_combination -hP
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hαβ
      · exact sub_eq_zero.mp h0
    have hfac := factor_eq hd h.left
    rw [hx, sub_self] at hfac h1
    simp only [mul_zero, sub_zero, ne_eq] at hfac h1
    have : (y - y₀) * (y - y₀) = 0 := by simpa using hfac
    exact h1 (mul_self_eq_zero.mp this)

section Group

variable [DecidableEq K]

lemma tc_neg (P : W.toAffine.Point) : tc W x₀ y₀ α (-P) = (tc W x₀ y₀ α P)⁻¹ := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← zero_def, _root_.neg_zero, tc_zero, inv_one]
  · rw [neg_some, tc_some, tc_some, negY, e₁, e₃, inv_div]
    obtain ⟨h1, h2⟩ := factors_ne_zero hd h
    have eA : -y - W.a₁ * x - W.a₃ - y₀ - α * (x - x₀) = -(y - y₀ - (-W.a₁ - α) * (x - x₀)) := by
      linear_combination -hd.hFY
    have eB : -y - W.a₁ * x - W.a₃ - y₀ - (-W.a₁ - α) * (x - x₀) = -(y - y₀ - α * (x - x₀)) := by
      linear_combination -hd.hFY
    rw [eA, eB, neg_div_neg_eq]

lemma tc_add (P Q : W.toAffine.Point) :
    tc W x₀ y₀ α (P + Q) = tc W x₀ y₀ α P * tc W x₀ y₀ α Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← zero_def, zero_add, tc_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← zero_def, add_zero, tc_zero, mul_one]
  obtain ⟨hA₁, hB₁⟩ := factors_ne_zero hd h₁
  obtain ⟨hA₂, hB₂⟩ := factors_ne_zero hd h₂
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  ·
    obtain ⟨hx, hy⟩ := hxy
    rw [add_of_Y_eq hx hy, tc_zero, tc_some, tc_some]
    rw [negY, e₁, e₃] at hy
    subst hx
    have eA : y₁ - y₀ - α * (x₁ - x₀) = -(y₂ - y₀ - (-W.a₁ - α) * (x₁ - x₀)) := by
      rw [hy]; linear_combination -hd.hFY
    have eB : y₁ - y₀ - (-W.a₁ - α) * (x₁ - x₀) = -(y₂ - y₀ - α * (x₁ - x₀)) := by
      rw [hy]; linear_combination -hd.hFY
    rw [eA, eB, eq_comm, div_mul_div_comm, div_eq_one_iff_eq]
    · ring
    · exact mul_ne_zero (neg_ne_zero.mpr hA₂) hB₂
  ·
    rw [add_some hxy, tc_some, tc_some, tc_some]
    set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hL
    set x₃ := W.toAffine.addX x₁ x₂ L with hx₃
    set μ := y₁ - L * x₁ with hμ

    have hcubic : (Cubic.mk (1 : K) (-L ^ 2 - W.a₁ * L + W.a₂)
        (2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄))
        (-x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)))
        = Cubic.mk 1 (-(x₁ + x₂ + x₃)) (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) (-(x₁ * x₂ * x₃)) := by
      have key := addPolynomial_slope h₁.left h₂.left hxy
      rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, e₁, e₂, e₃, e₄, e₆] at key
      exact (Cubic.toPoly_injective _ _).mp key
    simp only [Cubic.mk.injEq, true_and] at hcubic
    obtain ⟨hv₁, hv₂, hv₃⟩ := hcubic

    set ν := L * x₀ + μ - y₀ with hν

    have hs₁ : -L ^ 2 - W.a₁ * L + (3 * x₀ + W.a₂) = -((x₁ - x₀) + (x₂ - x₀) + (x₃ - x₀)) := by
      linear_combination hv₁
    have hs₂ : -(2 * L + W.a₁) * ν
        = (x₁ - x₀) * (x₂ - x₀) + (x₁ - x₀) * (x₃ - x₀) + (x₂ - x₀) * (x₃ - x₀) := by
      linear_combination hv₂ + 2 * x₀ * hv₁ + L * hd.hFY + hd.hFX
    have hs₃ : -ν ^ 2 = -((x₁ - x₀) * (x₂ - x₀) * (x₃ - x₀)) := by
      linear_combination hv₃ + x₀ * hv₂ + x₀ ^ 2 * hv₁ + ν * hd.hFY + hd.he

    have hy₂ : y₂ = L * x₂ + μ := by
      by_cases hx : x₁ = x₂
      · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
        have := Y_eq_of_Y_ne h₁.left h₂.left hx hy
        rw [hμ, ← hx, this]; ring
      · have hL' : L * (x₁ - x₂) = y₁ - y₂ := by
          rw [hL, slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
        rw [hμ]
        linear_combination hL'

    have h₃' : W.toAffine.Nonsingular x₃ (W.toAffine.negAddY x₁ x₂ y₁ L) :=
      nonsingular_negAdd h₁ h₂ hxy
    obtain ⟨hA₃, hB₃⟩ := factors_ne_zero hd h₃'
    have hnegAddY : W.toAffine.negAddY x₁ x₂ y₁ L = L * x₃ + μ := by
      simp only [negAddY, hμ]; ring
    rw [hnegAddY] at hA₃ hB₃

    have hprodA : (L * x₁ + μ - y₀ - α * (x₁ - x₀)) * (L * x₂ + μ - y₀ - α * (x₂ - x₀))
        * (L * x₃ + μ - y₀ - α * (x₃ - x₀)) = ν ^ 3 := by
      linear_combination (L - α) ^ 3 * hs₃ - ((L - α) ^ 2 * ν) * hs₂ + ((L - α) * ν ^ 2) * hs₁
        + (ν ^ 2 * (L - α)) * hd.hα
    have hprodB : (L * x₁ + μ - y₀ - (-W.a₁ - α) * (x₁ - x₀))
        * (L * x₂ + μ - y₀ - (-W.a₁ - α) * (x₂ - x₀))
        * (L * x₃ + μ - y₀ - (-W.a₁ - α) * (x₃ - x₀)) = ν ^ 3 := by
      have hβ : (-W.a₁ - α) ^ 2 + W.a₁ * (-W.a₁ - α) - (3 * x₀ + W.a₂) = 0 := by
        linear_combination hd.hα
      linear_combination (L - (-W.a₁ - α)) ^ 3 * hs₃ - ((L - (-W.a₁ - α)) ^ 2 * ν) * hs₂
        + ((L - (-W.a₁ - α)) * ν ^ 2) * hs₁ + (ν ^ 2 * (L - (-W.a₁ - α))) * hβ

    have hy₁ : y₁ = L * x₁ + μ := by rw [hμ]; ring
    simp only [addY, negY, negAddY, e₁, e₃]
    rw [← hx₃, hy₂, hy₁]
    rw [hy₁] at hA₁ hB₁
    rw [hy₂] at hA₂ hB₂
    have eNum : -(L * (x₃ - x₁) + (L * x₁ + μ)) - W.a₁ * x₃ - W.a₃ - y₀ - α * (x₃ - x₀)
        = -(L * x₃ + μ - y₀ - (-W.a₁ - α) * (x₃ - x₀)) := by
      linear_combination -hd.hFY
    have eDen : -(L * (x₃ - x₁) + (L * x₁ + μ)) - W.a₁ * x₃ - W.a₃ - y₀ - (-W.a₁ - α) * (x₃ - x₀)
        = -(L * x₃ + μ - y₀ - α * (x₃ - x₀)) := by
      linear_combination -hd.hFY
    rw [eNum, eDen, neg_div_neg_eq, div_mul_div_comm, div_eq_div_iff hA₃ (mul_ne_zero hB₁ hB₂)]
    linear_combination hprodB - hprodA

lemma tc_nsmul (P : W.toAffine.Point) (n : ℕ) :
    tc W x₀ y₀ α (n • P) = tc W x₀ y₀ α P ^ n := by
  induction n with
  | zero => rw [zero_smul, tc_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, tc_add hd, ih, pow_succ]

theorem eq_zero_of_prime_smul_eq_zero (hαβ : α ≠ -W.a₁ - α) {p : ℕ} [Fact p.Prime] [CharP K p]
    (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by
  apply eq_zero_of_tc_eq_one hd hαβ
  have h : tc W x₀ y₀ α P ^ p = 1 := by rw [← tc_nsmul hd, hP, tc_zero]

  have : (tc W x₀ y₀ α P - 1) ^ p = 0 := by rw [sub_pow_char, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp this)

theorem finite_and_ncard_torsion_le (hαβ : α ≠ -W.a₁ - α) {n : ℕ} (hn : 0 < n) :
    {P : W.toAffine.Point | n • P = 0}.Finite ∧ {P : W.toAffine.Point | n • P = 0}.ncard ≤ n := by
  set S : Set W.toAffine.Point := {P | n • P = 0} with hS

  have hinj : Set.InjOn (tc W x₀ y₀ α) S := by
    intro P _ Q _ hPQ
    have h1 : tc W x₀ y₀ α (P - Q) = 1 := by
      rw [sub_eq_add_neg, tc_add hd, tc_neg hd, hPQ, mul_inv_cancel₀ (tc_ne_zero hd Q)]
    exact sub_eq_zero.mp (eq_zero_of_tc_eq_one hd hαβ _ h1)
  set T : Finset K := (Polynomial.nthRoots n (1 : K)).toFinset with hT
  have himage : tc W x₀ y₀ α '' S ⊆ ↑T := by
    rintro _ ⟨P, hP, rfl⟩
    rw [hT, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, ← tc_nsmul hd]
    rw [hS, Set.mem_setOf_eq] at hP
    rw [hP, tc_zero]
  have hTfin : (↑T : Set K).Finite := T.finite_toSet
  have hfin : S.Finite := Set.Finite.of_finite_image (hTfin.subset himage) hinj
  refine ⟨hfin, ?_⟩
  calc S.ncard = (tc W x₀ y₀ α '' S).ncard := (hinj.ncard_image).symm
    _ ≤ (↑T : Set K).ncard := Set.ncard_le_ncard himage hTfin
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ Multiset.card (Polynomial.nthRoots n (1 : K)) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n 1

end Group

end NodalTorsion
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode.NodalTorsion"

namespace NodalTorsion

variable {k K : Type*} [Field k] [Field K] [DecidableEq k] [DecidableEq K]

noncomputable def toMap (W : WeierstrassCurve k) (f : k →+* K) (hf : Function.Injective f) :
    W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((Affine.map_nonsingular W hf x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
        add_of_Y_eq (congr_arg f hxy.left) (by rw [hxy.right, map_negY])]
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) :=
        fun h => hxy ⟨hf h.1, hf (by rw [map_negY] at h; exact h.2)⟩
      rw [add_some hxy, add_some hxy']
      simp only [map_slope, map_addX, map_addY]

lemma toMap_injective (W : WeierstrassCurve k) (f : k →+* K) (hf : Function.Injective f) :
    Function.Injective (toMap W f hf) := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨hf (some.inj h).left, hf (some.inj h).right⟩

end NodalTorsion
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode.NodalTorsion"

open NodalTorsion in

private lemma exists_frame {k : Type*} [Field k] (W : WeierstrassCurve k) (x₀ y₀ : k)
    (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀)
    (hnode : W.b₂ + 12 * x₀ ≠ 0) {K : Type*} [Field K] [IsAlgClosed K] (f : k →+* K)
    (hf : Function.Injective f) :
    ∃ α : K, Frame (W.map f) (f x₀) (f y₀) α ∧ α ≠ -(W.map f).a₁ - α := by

  rw [nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hFX, hFY⟩ := hs he
  rw [equation_iff] at he

  obtain ⟨α, hα⟩ : ∃ α : K, α ^ 2 + f W.a₁ * α - (3 * f x₀ + f W.a₂) = 0 := by
    let q : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (f W.a₁) * Polynomial.X
      - Polynomial.C (3 * f x₀ + f W.a₂)
    have hq : q.degree = 2 := by
      simp only [q]
      compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
    refine ⟨α, ?_⟩
    simpa [q] using hα
  refine ⟨α, ⟨?_, ?_, ?_, hα⟩, ?_⟩
  · show f y₀ ^ 2 + f W.a₁ * f x₀ * f y₀ + f W.a₃ * f y₀
      - (f x₀ ^ 3 + f W.a₂ * f x₀ ^ 2 + f W.a₄ * f x₀ + f W.a₆) = 0
    have := congrArg f he
    simp only [_root_.map_add, _root_.map_mul, _root_.map_pow] at this
    exact sub_eq_zero.mpr this
  · show f W.a₁ * f y₀ - (3 * f x₀ ^ 2 + 2 * f W.a₂ * f x₀ + f W.a₄) = 0
    have := congrArg f hFX
    simpa only [_root_.map_sub, _root_.map_mul, _root_.map_add, _root_.map_pow, map_ofNat,
      _root_.map_zero] using this
  · show 2 * f y₀ + f W.a₁ * f x₀ + f W.a₃ = 0
    have := congrArg f hFY
    simpa only [_root_.map_add, _root_.map_mul, map_ofNat, _root_.map_zero] using this
  ·
    intro hαβ
    change α = -f W.a₁ - α at hαβ
    apply hnode
    apply hf
    rw [_root_.map_add, _root_.map_mul, map_ofNat, _root_.map_zero]
    have h2 : 2 * α + f W.a₁ = 0 := by linear_combination hαβ
    have hb : f W.b₂ = (f W.a₁) ^ 2 + 4 * f W.a₂ := by
      simp only [WeierstrassCurve.b₂, _root_.map_add, _root_.map_mul, _root_.map_pow, map_ofNat]
    rw [hb]
    linear_combination (2 * α + f W.a₁) * h2 - 4 * hα

theorem solution {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0) {n : ℕ} (hn : 0 < n) : {P : W.toAffine.Point | n • P = 0}.Finite ∧ {P : W.toAffine.Point | n • P = 0}.ncard ≤ n := by
  classical
  let K := AlgebraicClosure k
  let f : k →+* K := algebraMap k K
  have hf : Function.Injective f := (algebraMap k K).injective
  obtain ⟨α, hd, hαβ⟩ := exists_frame W x₀ y₀ he hs hnode f hf
  obtain ⟨hfin', hcard'⟩ := NodalTorsion.finite_and_ncard_torsion_le hd hαβ hn
  set g := NodalTorsion.toMap W f hf with hg
  have hginj := NodalTorsion.toMap_injective W f hf
  have hmaps : g '' {P : W.toAffine.Point | n • P = 0} ⊆ {P | n • P = 0} := by
    rintro _ ⟨P, hP, rfl⟩
    rw [Set.mem_setOf_eq] at hP ⊢
    rw [← map_nsmul, hP, _root_.map_zero]
  have hinj : Set.InjOn g {P : W.toAffine.Point | n • P = 0} := hginj.injOn
  refine ⟨Set.Finite.of_finite_image (hfin'.subset hmaps) hinj, ?_⟩
  calc {P : W.toAffine.Point | n • P = 0}.ncard
      = (g '' {P : W.toAffine.Point | n • P = 0}).ncard := (hinj.ncard_image).symm
    _ ≤ {P : (W.map f).toAffine.Point | n • P = 0}.ncard := Set.ncard_le_ncard hmaps hfin'
    _ ≤ n := hcard'

end S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_finite_and_ncard_torsion_le_of_isNode (solution)
