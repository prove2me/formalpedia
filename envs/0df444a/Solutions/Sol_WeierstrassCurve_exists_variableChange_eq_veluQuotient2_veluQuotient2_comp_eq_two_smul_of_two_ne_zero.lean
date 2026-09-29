-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7110faba-1c5c-5ad1-a4ff-a7aa810ddee9

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace VeluTwoDualC3

section PointHelpers

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in

private lemma nonsingular_vc_of_eq {C : VariableChange F} {W V : Affine F} (h : C • W = V) {x y : F}
    (hns : V.Nonsingular x y) : W.Nonsingular (vcX C x) (vcY C x y) := by
  subst h; exact (nonsingular_variableChange_iff x y).mp hns

private lemma equivOfVariableChangeEq_zero {C : VariableChange F} {W V : Affine F} (h : C • W = V) :
    equivOfVariableChangeEq h (0 : V.Point) = 0 := by
  subst h; rfl

private lemma equivOfVariableChangeEq_zero' {C : VariableChange F} {W V : Affine F} (h : C • W = V) :
    equivOfVariableChangeEq h (.zero : V.Point) = .zero := by
  subst h; rfl

omit [DecidableEq F] in

private lemma vcFun_zero' (C : VariableChange F) (W : Affine F) :
    vcFun C W (.zero : (C • W).toAffine.Point) = .zero := rfl

private lemma equivOfVariableChangeEq_some {C : VariableChange F} {W V : Affine F} (h : C • W = V)
    {x y : F} (hns : V.Nonsingular x y) (hns' : W.Nonsingular (vcX C x) (vcY C x y)) :
    equivOfVariableChangeEq h (.some x y hns) = .some (vcX C x) (vcY C x y) hns' := by
  subst h; rfl

omit [DecidableEq F] in

private lemma vcFun_some (C : VariableChange F) (W : Affine F) {x y : F}
    (hns : (C • W).toAffine.Nonsingular x y) (hns' : W.Nonsingular (vcX C x) (vcY C x y)) :
    vcFun C W (.some x y hns) = .some (vcX C x) (vcY C x y) hns' := rfl

omit [DecidableEq F] in

private lemma vcInvFun_some (C : VariableChange F) (W : Affine F) {x y : F}
    (hns : W.Nonsingular x y) (hns' : (C • W).toAffine.Nonsingular (vcXInv C x) (vcYInv C x y)) :
    vcInvFun C W (.some x y hns) = .some (vcXInv C x) (vcYInv C x y) hns' := rfl

private noncomputable def vcInvHom (C : VariableChange F) (W : Affine F) :
    W.Point →+ (C • W).toAffine.Point where
  toFun := vcInvFun C W
  map_zero' := rfl
  map_add' := vcInvFun_add C W

private lemma vcInvHom_apply (C : VariableChange F) (W : Affine F) (P : W.Point) :
    vcInvHom C W P = vcInvFun C W P := rfl

private lemma vcFun_two_zsmul_vcInvFun (C : VariableChange F) (W : Affine F) (P : W.Point) :
    vcFun C W ((2 : ℤ) • vcInvFun C W P) = (2 : ℤ) • P := by
  have h : (2 : ℤ) • vcInvFun C W P = vcInvFun C W ((2 : ℤ) • P) := by
    rw [← vcInvHom_apply, ← vcInvHom_apply, map_zsmul]
  rw [h]
  exact vcFun_rightInverse ((2 : ℤ) • P)

omit [DecidableEq F] in

private lemma some_ext {W' : Affine F} {x₁ x₂ y₁ y₂ : F} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

omit [DecidableEq F] in

private lemma eq_zero_of_eq_neg (h2 : (2 : F) ≠ 0) {z : F} (h : z = -z) : z = 0 := by
  have : (2 : F) * z = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

omit [DecidableEq F] in

private lemma negY_of_isCharNeTwoNF {W : WeierstrassCurve F} [W.IsCharNeTwoNF] (x y : F) :
    W.toAffine.negY x y = -y := by
  rw [Affine.negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

private theorem two_zsmul_some_zero_eq_zero_of_isCharNeTwoNF {W : WeierstrassCurve F} [W.IsCharNeTwoNF]
    {e : F} (h : W.toAffine.Nonsingular e 0) :
    (2 : ℤ) • (Point.some e 0 h : W.toAffine.Point) = 0 := by
  rw [two_zsmul]
  apply add_self_of_Y_eq
  rw [negY_of_isCharNeTwoNF]
  exact _root_.neg_zero.symm

end PointHelpers

section NFBasics

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma equation_zero_iff (x : F) :
    W.toAffine.Equation x 0 ↔ x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := by
  rw [Affine.equation_iff]
  constructor <;> intro h <;> linear_combination -h

variable [W.IsCharNeTwoNF]

private lemma veluGy_zero (x : F) : W.veluGy x 0 = 0 := by
  simp [veluGy, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]

private lemma eq_zero_of_veluGy_eq_zero (h2 : (2 : F) ≠ 0) {x y : F} (h : W.veluGy x y = 0) : y = 0 := by
  simp only [veluGy, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, zero_mul, add_zero,
    neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_left h2

private lemma equation_iff_a₂form (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  have h1 := a₁_of_isCharNeTwoNF (W := W)
  have h3 := a₃_of_isCharNeTwoNF (W := W)
  rw [Affine.equation_iff]
  constructor
  · intro h
    linear_combination h - x * y * h1 - y * h3
  · intro h
    linear_combination h + x * y * h1 + y * h3

private scoped instance isCharNeTwoNF_veluQuotient2 (x₀ y₀ : F) :
    (W.veluQuotient2 x₀ y₀).IsCharNeTwoNF :=
  ⟨by simp [veluQuotient2_a₁, a₁_of_isCharNeTwoNF],
   by simp [veluQuotient2_a₃, a₃_of_isCharNeTwoNF]⟩

private theorem velu2Y_zero (x₀ x : F) : W.velu2Y x₀ 0 x 0 = 0 := by
  simp only [velu2Y, a₁_of_isCharNeTwoNF, zero_mul, mul_zero, add_zero, sub_self, zero_div]

end NFBasics

section DataLayer

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma veluGx_at_zero (x : F) : W.veluGx x 0 = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [veluGx]

private theorem veluGx_quotient_x₁ (e : F) :
    (W.veluQuotient2 e 0).veluGx (-2 * e - W.a₂) 0
      = W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄ := by
  simp only [veluGx_at_zero, veluQuotient2_a₂, veluQuotient2_a₄]
  ring

variable [W.IsCharNeTwoNF] {e : F} (he : e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆ = 0)

include he in

private theorem neg_root_of_quotient :
    (-2 * e - W.a₂) ^ 3 + W.a₂ * (-2 * e - W.a₂) ^ 2
      + (W.veluQuotient2 e 0).a₄ * (-2 * e - W.a₂) + (W.veluQuotient2 e 0).a₆ = 0 := by
  simp only [veluQuotient2_a₄, veluQuotient2_a₆, veluGx_at_zero, b₂_of_isCharNeTwoNF]
  linear_combination he

include he in
omit [W.IsCharNeTwoNF] in

private theorem other_roots_quadratic_factorization (x : F) :
    (x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))
      = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  linear_combination -he

omit [W.IsCharNeTwoNF] in
include he in

private theorem other_roots_quadratic_eq_zero {f : F}
    (hf : f ^ 3 + W.a₂ * f ^ 2 + W.a₄ * f + W.a₆ = 0) (hne : f ≠ e) :
    f ^ 2 + (e + W.a₂) * f + (e ^ 2 + W.a₂ * e + W.a₄) = 0 := by
  have hd : f - e ≠ 0 := sub_ne_zero.mpr hne
  have key : (f - e) * (f ^ 2 + (e + W.a₂) * f + (e ^ 2 + W.a₂ * e + W.a₄)) = 0 := by
    rw [other_roots_quadratic_factorization W he]; exact hf
  exact (mul_eq_zero.mp key).resolve_left hd

omit [W.IsCharNeTwoNF] in
include he in

private theorem velu2X_other_root {f : F}
    (hf : f ^ 3 + W.a₂ * f ^ 2 + W.a₄ * f + W.a₆ = 0) (hne : f ≠ e) :
    W.velu2X e 0 f = -2 * e - W.a₂ := by
  have hd : f - e ≠ 0 := sub_ne_zero.mpr hne
  have hQ0 := other_roots_quadratic_eq_zero W he hf hne
  rw [velu2X, veluGx_at_zero]
  field_simp
  linear_combination hQ0

omit [W.IsCharNeTwoNF] in

private theorem doubleQuotient_a₄ :
    ((W.veluQuotient2 e 0).veluQuotient2 (-2 * e - W.a₂) 0).a₄
      = 16 * W.a₄ - 5 * W.a₂ ^ 2 := by
  simp only [veluQuotient2_a₄, veluQuotient2_a₂, veluGx_at_zero]
  ring

include he in

private theorem doubleQuotient_a₆ :
    ((W.veluQuotient2 e 0).veluQuotient2 (-2 * e - W.a₂) 0).a₆
      = 64 * W.a₆ - 16 * W.a₂ * W.a₄ + 3 * W.a₂ ^ 3 := by
  simp only [veluQuotient2_a₆, veluQuotient2_a₄, veluQuotient2_a₂,
    b₂_of_isCharNeTwoNF, veluGx_at_zero]
  linear_combination (-63 : F) * he

private def halfShift (h2 : (2 : F) ≠ 0) (W : WeierstrassCurve F) : VariableChange F :=
  ⟨(Units.mk0 2 h2)⁻¹, -(W.a₂ / 4), 0, 0⟩

omit [W.IsCharNeTwoNF] in
private lemma halfShift_u (h2 : (2 : F) ≠ 0) :
    (((halfShift h2 W).u : Fˣ) : F) = 2⁻¹ := by
  simp only [halfShift, Units.val_inv_eq_inv_val, Units.val_mk0]

omit [W.IsCharNeTwoNF] in
private lemma halfShift_u_inv (h2 : (2 : F) ≠ 0) :
    (((halfShift h2 W).u⁻¹ : Fˣ) : F) = 2 := by
  simp only [halfShift, inv_inv, Units.val_mk0]

include he in

private theorem halfShift_smul_eq_doubleQuotient (h2 : (2 : F) ≠ 0) :
    (halfShift h2 W) • W = (W.veluQuotient2 e 0).veluQuotient2 (-2 * e - W.a₂) 0 := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero h2 h2
  ext
  · simp only [variableChange_a₁, a₁_of_isCharNeTwoNF, halfShift, mul_zero, add_zero]
  · rw [variableChange_a₂, veluQuotient2_a₂, veluQuotient2_a₂]
    simp only [halfShift, inv_inv, Units.val_mk0, a₁_of_isCharNeTwoNF, mul_zero, sub_zero]
    field_simp
    ring
  · simp only [variableChange_a₃, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, halfShift,
      mul_zero, add_zero]
  · rw [variableChange_a₄, doubleQuotient_a₄ W]
    simp only [halfShift, inv_inv, Units.val_mk0, a₁_of_isCharNeTwoNF,
      a₃_of_isCharNeTwoNF, mul_zero, sub_zero, add_zero]
    field_simp
    ring
  · rw [variableChange_a₆, doubleQuotient_a₆ W he]
    simp only [halfShift, inv_inv, Units.val_mk0, a₁_of_isCharNeTwoNF,
      a₃_of_isCharNeTwoNF, mul_zero, sub_zero]
    field_simp
    ring

end DataLayer

section SeamRing

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private theorem doubleQuot_xCore (e x : F) :
    (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))
          * (x * (x - e) + (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
        + (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2
        - (3 * W.a₂ + 8 * x) * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))) := by
  ring

private theorem doubleQuot_yCore (e x : F) :
    ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
        * ((x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2
            - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2)
      = -(3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 3
        + 4 * (W.a₂ + 3 * x)
            * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))
            * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
        - 8 * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))) ^ 2 := by
  ring

variable {e x y : F}

private theorem velu2X_mul_sub (hne : x ≠ e) :
    W.velu2X e 0 x * (x - e) = x * (x - e) + (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄) := by
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, veluGx_at_zero, add_mul, div_mul_cancel₀ _ hd]

private theorem velu2X_sub_x₁_mul_sub (hne : x ≠ e) :
    (W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e)
      = x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄) := by
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, veluGx_at_zero, sub_mul, add_mul, div_mul_cancel₀ _ hd]
  ring

variable (he : e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆ = 0)
  (hP : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) (hy : y ≠ 0)

include he hP in

private theorem ySq_eq_mul_quadratic :
    y ^ 2 = (x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) := by
  linear_combination hP + he

include he hP hy in

private theorem ne_e_of_y_ne_zero : x ≠ e := by
  intro hxe; subst hxe
  exact hy (pow_eq_zero_iff two_ne_zero |>.mp (hP.trans he))

include he hP hy in

private theorem other_roots_quadratic_ne_zero :
    x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄) ≠ 0 := by
  intro hQ
  have hy2 : y ^ 2 = 0 := by rw [ySq_eq_mul_quadratic W he hP, hQ, mul_zero]
  exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)

include he hP hy in

private theorem velu2X_ne_x₁ : W.velu2X e 0 x ≠ -2 * e - W.a₂ := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hQne := other_roots_quadratic_ne_zero W he hP hy
  intro heq
  apply hQne
  rw [← velu2X_sub_x₁_mul_sub W hxe, heq, sub_self, zero_mul]

end SeamRing

section SeamInterface

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.IsCharNeTwoNF]
variable {e x y : F} (he : e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆ = 0)
  (hP : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) (hy : y ≠ 0)

include he hP hy in

private theorem doubleQuot_xCoord_eq (h2 : (2 : F) ≠ 0) :
    (W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
      = 4 * W.toAffine.addX x x (W.toAffine.slope x x y y) + W.a₂ := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hQne := other_roots_quadratic_ne_zero W he hP hy
  have hc := ySq_eq_mul_quadratic W he hP
  have hYne : y ≠ W.toAffine.negY x y := by
    rw [negY_of_isCharNeTwoNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hX1p_ne : W.velu2X e 0 x - (-2 * e - W.a₂) ≠ 0 := fun h => hQne (by
    rw [← velu2X_sub_x₁_mul_sub W hxe, h, zero_mul])

  have step : (W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
        * (W.velu2X e 0 x - (-2 * e - W.a₂))
      = W.velu2X e 0 x * (W.velu2X e 0 x - (-2 * e - W.a₂))
        + (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) := by
    rw [velu2X, veluGx_quotient_x₁, add_mul, div_mul_cancel₀ _ hX1p_ne]

  have hX2_clear : (W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
        * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))
      = (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))
          * (x * (x - e) + (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
        + (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2 := by
    have h1 : (W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
          * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))
        = (W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
          * (W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e) ^ 2 := by
      rw [← velu2X_sub_x₁_mul_sub W hxe]; ring
    rw [h1, step, add_mul,
      show W.velu2X e 0 x * (W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e) ^ 2
        = (W.velu2X e 0 x * (x - e)) * ((W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e)) from by
          ring,
      velu2X_mul_sub W hxe, velu2X_sub_x₁_mul_sub W hxe]
    ring

  have haddX : 4 * W.toAffine.addX x x (W.toAffine.slope x x y y) * y ^ 2
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 - 4 * (W.a₂ + 2 * x) * y ^ 2 := by
    have key : ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y)) ^ 2 * (2 * y) ^ 2
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
      rw [div_pow]; exact div_mul_cancel₀ _ (pow_ne_zero 2 h2y)
    rw [slope_of_Y_ne rfl hYne, addX, a₁_of_isCharNeTwoNF, negY_of_isCharNeTwoNF,
      show y - -y = 2 * y from by ring]
    linear_combination key

  have hdenom :
      y ^ 2 * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hy) (mul_ne_zero hd hQne)
  refine mul_left_cancel₀ hdenom ?_
  linear_combination (y ^ 2) * hX2_clear + (y ^ 2) * doubleQuot_xCore W e x
    + (-((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))) * haddX
    + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 * hc

include he hP hy in

private theorem doubleQuot_yCoord_eq (h2 : (2 : F) ≠ 0) :
    (W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
      = 8 * W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hQne := other_roots_quadratic_ne_zero W he hP hy
  have hc := ySq_eq_mul_quadratic W he hP
  have hYne : y ≠ W.toAffine.negY x y := by
    rw [negY_of_isCharNeTwoNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy
  have hX1p_ne : W.velu2X e 0 x - (-2 * e - W.a₂) ≠ 0 := fun h => hQne (by
    rw [← velu2X_sub_x₁_mul_sub W hxe, h, zero_mul])

  have hY1_clear : W.velu2Y e 0 x y * (x - e) ^ 2
      = y * ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄)) := by
    rw [velu2Y, veluGx_at_zero, a₁_of_isCharNeTwoNF, zero_mul, zero_add, sub_zero, sub_mul,
      mul_div_assoc, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
    ring

  have stepY :
      (W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
        * (W.velu2X e 0 x - (-2 * e - W.a₂)) ^ 2
      = W.velu2Y e 0 x y
        * ((W.velu2X e 0 x - (-2 * e - W.a₂)) ^ 2
            - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄)) := by
    rw [velu2Y, veluGx_quotient_x₁, veluQuotient2_a₁, a₁_of_isCharNeTwoNF, zero_mul, zero_add,
      sub_zero, sub_mul, mul_div_assoc, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hX1p_ne)]
    ring

  have hY2_clear :
      (W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
        * ((x - e) ^ 2 * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2)
      = y * ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
        * ((x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2
            - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2) := by
    have h1 :
        (W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
          * ((x - e) ^ 2 * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2)
        = (W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
          * (W.velu2X e 0 x - (-2 * e - W.a₂)) ^ 2 * (x - e) ^ 4 := by
      rw [← velu2X_sub_x₁_mul_sub W hxe]; ring
    rw [h1, stepY]
    have h2sq : ((W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e)) ^ 2
        = (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2 := by
      rw [velu2X_sub_x₁_mul_sub W hxe]
    calc W.velu2Y e 0 x y
            * ((W.velu2X e 0 x - (-2 * e - W.a₂)) ^ 2
                - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄))
            * (x - e) ^ 4
        = (W.velu2Y e 0 x y * (x - e) ^ 2)
            * (((W.velu2X e 0 x - (-2 * e - W.a₂)) * (x - e)) ^ 2
              - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2) := by ring
      _ = y * ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
            * ((x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2
              - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2) := by
          rw [hY1_clear, h2sq]

  have haddY : 8 * W.toAffine.addY x x y (W.toAffine.slope x x y y) * y ^ 3
      = -(3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 3
        + 4 * (W.a₂ + 3 * x) * y ^ 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) - 8 * y ^ 4 := by
    have key1 : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y) * (2 * y)
        = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := div_mul_cancel₀ _ h2y
    have key3 : ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y)) ^ 3 * (2 * y) ^ 3
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 3 := by
      rw [div_pow]; exact div_mul_cancel₀ _ (pow_ne_zero 3 h2y)
    rw [slope_of_Y_ne rfl hYne, addY, negAddY, addX, negY, a₁_of_isCharNeTwoNF,
      a₃_of_isCharNeTwoNF, negY_of_isCharNeTwoNF, show y - -y = 2 * y from by ring]
    linear_combination (-1 : F) * key3 + (4 * (W.a₂ + 3 * x) * y ^ 2) * key1

  have hdenom : y ^ 3
      * ((x - e) ^ 2 * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hy) (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 2 hQne))

  obtain ⟨R, hR⟩ : ∃ R : F, R = -(3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 3
        + 4 * (W.a₂ + 3 * x)
            * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))
            * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
        - 8 * ((x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))) ^ 2 :=
    ⟨_, rfl⟩
  have hAB : ((x - e) ^ 2 - (3 * e ^ 2 + 2 * W.a₂ * e + W.a₄))
        * ((x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2
            - (W.a₂ ^ 2 - 3 * e ^ 2 - 2 * W.a₂ * e - 4 * W.a₄) * (x - e) ^ 2) = R := by
    rw [hR]; exact doubleQuot_yCore W e x
  have e2 : 8 * W.toAffine.addY x x y (W.toAffine.slope x x y y) * y ^ 3 = R := by
    rw [hR]
    linear_combination haddY
      + (4 * (W.a₂ + 3 * x) * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
          - 8 * (y ^ 2 + (x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)))) * hc
  refine mul_left_cancel₀ hdenom ?_
  linear_combination (y ^ 3) * hY2_clear + (y ^ 4) * hAB
    - ((x - e) ^ 2 * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄)) ^ 2) * e2
    + (y ^ 2 + (x - e) * (x ^ 2 + (e + W.a₂) * x + (e ^ 2 + W.a₂ * e + W.a₄))) * R * hc

omit [DecidableEq F] [W.IsCharNeTwoNF] in

private lemma vcX_halfShift (h2 : (2 : F) ≠ 0) (z : F) :
    vcX (halfShift h2 W) z = (2 : F)⁻¹ ^ 2 * z + -(W.a₂ / 4) := by
  simp only [vcX, halfShift, Units.val_inv_eq_inv_val, Units.val_mk0]

omit [DecidableEq F] [W.IsCharNeTwoNF] in

private lemma vcY_halfShift (h2 : (2 : F) ≠ 0) (z w : F) :
    vcY (halfShift h2 W) z w = (2 : F)⁻¹ ^ 3 * w := by
  simp only [vcY, halfShift, Units.val_inv_eq_inv_val, Units.val_mk0, add_zero, mul_zero,
    zero_mul]

include he hP hy in

private theorem vc_xCoord_eq (h2 : (2 : F) ≠ 0) :
    vcX (halfShift h2 W)
        ((W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x))
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero h2 h2
  rw [vcX_halfShift, doubleQuot_xCoord_eq W he hP hy h2]
  field_simp
  ring

include he hP hy in

private theorem vc_yCoord_eq (h2 : (2 : F) ≠ 0) :
    vcY (halfShift h2 W)
        ((W.veluQuotient2 e 0).velu2X (-2 * e - W.a₂) 0 (W.velu2X e 0 x))
        ((W.veluQuotient2 e 0).velu2Y (-2 * e - W.a₂) 0 (W.velu2X e 0 x)
          (W.velu2Y e 0 x y))
      = W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
  rw [vcY_halfShift, doubleQuot_yCoord_eq W he hP hy h2]
  field_simp
  ring

end SeamInterface

section CoreCharNeTwo

variable {F : Type*} [Field F] [DecidableEq F]

private theorem core (h2 : (2 : F) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ (x₁ y₁ : F) (hQ₁ : (W.veluQuotient2 x₀ y₀).toAffine.Equation x₁ y₁)
      (hgy₁ : (W.veluQuotient2 x₀ y₀).veluGy x₁ y₁ = 0)
      (hΔ₁ : ((W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁).Δ ≠ 0)
      (C : VariableChange F) (hC : C • W = (W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁),
      (∀ x y : F, W.toAffine.Equation x y → W.veluGy x y = 0 → x ≠ x₀ →
          W.velu2X x₀ y₀ x = x₁ ∧ W.velu2Y x₀ y₀ x y = y₁) ∧
      ∀ P : W.toAffine.Point,
        equivOfVariableChangeEq hC
            (veluPointMap2 h2 hQ₁ hgy₁ hΔ₁ (veluPointMap2 h2 hQ hgy hΔ P))
          = (2 : ℤ) • P := by

  obtain rfl : y₀ = 0 := eq_zero_of_veluGy_eq_zero W h2 hgy

  have he : x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ = 0 := (equation_zero_iff W x₀).mp hQ

  have hR' : (W.veluQuotient2 x₀ 0).toAffine.Equation (-2 * x₀ - W.a₂) 0 := by
    rw [equation_zero_iff, veluQuotient2_a₂]; exact neg_root_of_quotient W he
  have hgyR' : (W.veluQuotient2 x₀ 0).veluGy (-2 * x₀ - W.a₂) 0 = 0 :=
    veluGy_zero (W.veluQuotient2 x₀ 0) (-2 * x₀ - W.a₂)

  have hC : (halfShift h2 W) • W
      = (W.veluQuotient2 x₀ 0).veluQuotient2 (-2 * x₀ - W.a₂) 0 :=
    halfShift_smul_eq_doubleQuotient W he h2
  have hΔ'' : ((W.veluQuotient2 x₀ 0).veluQuotient2 (-2 * x₀ - W.a₂) 0).Δ ≠ 0 := by
    rw [← hC, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) W.isUnit_Δ.ne_zero
  refine ⟨-2 * x₀ - W.a₂, 0, hR', hgyR', hΔ'', halfShift h2 W, hC, ?_, fun P => ?_⟩
  ·
    intro x y hxy hgyxy hne
    obtain rfl : y = 0 := eq_zero_of_veluGy_eq_zero W h2 hgyxy
    have hx_root : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := (equation_zero_iff W x).mp hxy
    exact ⟨velu2X_other_root W he hx_root hne, velu2Y_zero W x₀ x⟩

  rcases P with _ | ⟨x, y, hns⟩
  ·
    rw [veluPointMap2_zero, veluPointMap2_zero, equivOfVariableChangeEq_zero' hC]
    exact (zsmul_zero (2 : ℤ)).symm
  ·
    have hPeq : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (equation_iff_a₂form W x y).mp hns.1
    by_cases hy : y = 0
    ·
      subst hy
      rw [two_zsmul_some_zero_eq_zero_of_isCharNeTwoNF hns]
      by_cases hxe : x = x₀
      ·
        rw [veluPointMap2_some_of_eq h2 hQ hgy hΔ hns hxe, veluPointMap2_zero]
        exact equivOfVariableChangeEq_zero hC
      ·
        have hx_root : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := by linear_combination -hPeq
        have hX1 : W.velu2X x₀ 0 x = -2 * x₀ - W.a₂ := velu2X_other_root W he hx_root hxe
        have hnsQ' := velu2_map_nonsingular h2 hns.1 hQ hgy hxe hΔ
        rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hns hxe,
          veluPointMap2_some_of_eq h2 hR' hgyR' hΔ'' hnsQ' hX1]
        exact equivOfVariableChangeEq_zero hC
    ·
      have hxe : x ≠ x₀ := ne_e_of_y_ne_zero W he hPeq hy
      have hX1_ne : W.velu2X x₀ 0 x ≠ -2 * x₀ - W.a₂ := velu2X_ne_x₁ W he hPeq hy
      have hYne : y ≠ W.toAffine.negY x y := by
        rw [negY_of_isCharNeTwoNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)

      rw [two_zsmul, add_self_of_Y_ne hYne]

      have hnsQ' := velu2_map_nonsingular h2 hns.1 hQ hgy hxe hΔ
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hns hxe,
        veluPointMap2_some_of_ne h2 hR' hgyR' hΔ'' hnsQ' hX1_ne]
      have hnsQ'' := velu2_map_nonsingular h2 hnsQ'.1 hR' hgyR' hX1_ne hΔ''
      have hnsW := nonsingular_vc_of_eq hC hnsQ''
      rw [equivOfVariableChangeEq_some hC hnsQ'' hnsW]
      exact some_ext (vc_xCoord_eq W he hPeq hy h2) (vc_yCoord_eq W he hPeq hy h2)

end CoreCharNeTwo

section VCCompat

variable {F : Type*} [Field F]
variable (C : VariableChange F) (W : WeierstrassCurve F) {x₀ y₀ : F}

private theorem variableChange_veluGx_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    (C • W).veluGx (vcXInv C x₀) (vcYInv C x₀ y₀)
      = ((C.u⁻¹ : Fˣ) : F) ^ 4 * W.veluGx x₀ y₀ := by
  rw [variableChange_veluGx, hgy, mul_zero, add_zero]

private theorem variableChange_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    (C • W).veluGy (vcXInv C x₀) (vcYInv C x₀ y₀) = 0 := by
  rw [variableChange_veluGy, hgy, mul_zero]

private theorem variableChange_veluQuotient2_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    (C • W).veluQuotient2 (vcXInv C x₀) (vcYInv C x₀ y₀) = C • (W.veluQuotient2 x₀ y₀) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hgx := variableChange_veluGx_of_veluGy_eq_zero C W hgy
  ext
  · simp only [veluQuotient2_a₁, variableChange_a₁]
  · simp only [veluQuotient2_a₂, variableChange_a₂, veluQuotient2_a₁]
  · simp only [veluQuotient2_a₃, variableChange_a₃, veluQuotient2_a₁]
  · simp only [veluQuotient2_a₄, variableChange_a₄, veluQuotient2_a₁, veluQuotient2_a₂,
      veluQuotient2_a₃, hgx, Units.val_inv_eq_inv_val]
    field_simp; ring
  · simp only [veluQuotient2_a₆, hgx]
    simp only [variableChange_a₆, variableChange_a₁, variableChange_a₂, veluQuotient2_a₁,
      veluQuotient2_a₂, veluQuotient2_a₃, veluQuotient2_a₄, veluQuotient2_a₆, b₂, vcXInv,
      Units.val_inv_eq_inv_val]
    field_simp; ring

private theorem vcXInv_sub_vcXInv (x x₀ : F) :
    vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - x₀) := by
  simp only [vcXInv]; ring

private theorem variableChange_velu2X_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) {x : F}
    (hne : x ≠ x₀) :
    (C • W).velu2X (vcXInv C x₀) (vcYInv C x₀ y₀) (vcXInv C x)
      = vcXInv C (W.velu2X x₀ y₀ x) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, velu2X, variableChange_veluGx_of_veluGy_eq_zero C W hgy,
    vcXInv_sub_vcXInv]
  simp only [vcXInv, Units.val_inv_eq_inv_val]
  field_simp; ring

private theorem variableChange_velu2Y_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) {x : F}
    (hne : x ≠ x₀) (y : F) :
    (C • W).velu2Y (vcXInv C x₀) (vcYInv C x₀ y₀) (vcXInv C x) (vcYInv C x y)
      = vcYInv C (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2Y, velu2Y, velu2X, variableChange_veluGx_of_veluGy_eq_zero C W hgy,
    vcXInv_sub_vcXInv]
  simp only [vcYInv, variableChange_a₁, Units.val_inv_eq_inv_val]
  field_simp; ring

end VCCompat

section Conj

variable {F : Type*} [Field F]

private theorem vcX_conj (D C₀ : VariableChange F) (z : F) :
    vcX (D⁻¹ * C₀ * D) z = vcX D (vcX C₀ (vcXInv D z)) := by
  have huD : (D.u : F) ≠ 0 := D.u.ne_zero
  have huC : (C₀.u : F) ≠ 0 := C₀.u.ne_zero
  simp only [vcX, vcXInv, VariableChange.mul_def, VariableChange.inv_def,
    Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp; ring

private theorem vcY_conj (D C₀ : VariableChange F) (z w : F) :
    vcY (D⁻¹ * C₀ * D) z w
      = vcY D (vcX C₀ (vcXInv D z)) (vcY C₀ (vcXInv D z) (vcYInv D z w)) := by
  have huD : (D.u : F) ≠ 0 := D.u.ne_zero
  have huC : (C₀.u : F) ≠ 0 := C₀.u.ne_zero
  simp only [vcX, vcY, vcXInv, vcYInv, VariableChange.mul_def, VariableChange.inv_def,
    Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp; ring

end Conj

end VeluTwoDualC3
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero.VeluTwoDualC3"

open VeluTwoDualC3

theorem solution
    {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ (x₁ y₁ : K) (hQ₁ : (W.veluQuotient2 x₀ y₀).toAffine.Equation x₁ y₁)
      (hgy₁ : (W.veluQuotient2 x₀ y₀).veluGy x₁ y₁ = 0)
      (hΔ₁ : ((W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁).Δ ≠ 0)
      (C : VariableChange K) (hC : C • W = (W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁),
      (∀ x y : K, W.toAffine.Equation x y → W.veluGy x y = 0 → x ≠ x₀ →
          W.velu2X x₀ y₀ x = x₁ ∧ W.velu2Y x₀ y₀ x y = y₁) ∧
      ∀ P : W.toAffine.Point,
        Point.equivOfVariableChangeEq hC
            (veluPointMap2 h2 hQ₁ hgy₁ hΔ₁ (veluPointMap2 h2 hQ hgy hΔ P))
          = (2 : ℤ) • P := by

  letI : Invertible (2 : K) := invertibleOfNonzero h2
  set D := W.toCharNeTwoNF with hD_def

  haveI hE₀ : (D • W).IsElliptic := inferInstance
  haveI hNF₀ : (D • W).IsCharNeTwoNF := hD_def ▸ W.toCharNeTwoNF_spec
  clear_value D; clear hD_def

  have hQ₀ : (D • W).toAffine.Equation (vcXInv D x₀) (vcYInv D x₀ y₀) :=
    (equation_variableChange_iff _ _).mpr (by rw [vcX_vcXInv, vcY_vcYInv]; exact hQ)
  have hgy₀ : (D • W).veluGy (vcXInv D x₀) (vcYInv D x₀ y₀) = 0 :=
    variableChange_veluGy_eq_zero D W hgy

  have hW'eq : (D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)
      = D • (W.veluQuotient2 x₀ y₀) :=
    variableChange_veluQuotient2_of_veluGy_eq_zero D W hgy
  have hΔ₀' : ((D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)).Δ ≠ 0 := by
    rw [hW'eq, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ

  obtain ⟨X₁, Y₁, hR'₀, hgyR'₀, hΔ₀'', C₀, hC₀, clause₀, seam₀⟩ := core h2 (D • W) hQ₀ hgy₀ hΔ₀'

  have hR'₁ : (D • W.veluQuotient2 x₀ y₀).toAffine.Equation X₁ Y₁ := by
    rw [← hW'eq]; exact hR'₀
  have hR' : (W.veluQuotient2 x₀ y₀).toAffine.Equation (vcX D X₁) (vcY D X₁ Y₁) :=
    (equation_variableChange_iff X₁ Y₁).mp hR'₁
  have hgyR' : (W.veluQuotient2 x₀ y₀).veluGy (vcX D X₁) (vcY D X₁ Y₁) = 0 := by
    have h : (D • (W.veluQuotient2 x₀ y₀)).veluGy X₁ Y₁ = 0 := by rw [← hW'eq]; exact hgyR'₀
    rw [show X₁ = vcXInv D (vcX D X₁) from (vcXInv_vcX X₁).symm,
      show Y₁ = vcYInv D (vcX D X₁) (vcY D X₁ Y₁) from (vcYInv_vcY X₁ Y₁).symm,
      variableChange_veluGy, mul_eq_zero] at h
    exact h.resolve_left (pow_ne_zero 3 D.u⁻¹.ne_zero)

  have hW''eq :
      ((D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)).veluQuotient2 X₁ Y₁
        = D • ((W.veluQuotient2 x₀ y₀).veluQuotient2 (vcX D X₁) (vcY D X₁ Y₁)) := by
    rw [hW'eq]
    conv_lhs => rw [show X₁ = vcXInv D (vcX D X₁) from (vcXInv_vcX X₁).symm,
      show Y₁ = vcYInv D (vcX D X₁) (vcY D X₁ Y₁) from (vcYInv_vcY X₁ Y₁).symm]
    exact variableChange_veluQuotient2_of_veluGy_eq_zero D _ hgyR'
  have hΔ'' : ((W.veluQuotient2 x₀ y₀).veluQuotient2 (vcX D X₁) (vcY D X₁ Y₁)).Δ ≠ 0 := by
    have h := hΔ₀''
    rw [hW''eq, variableChange_Δ] at h
    exact right_ne_zero_of_mul h

  have hC : (D⁻¹ * C₀ * D) • W
      = (W.veluQuotient2 x₀ y₀).veluQuotient2 (vcX D X₁) (vcY D X₁ Y₁) := by
    rw [mul_smul, mul_smul, hC₀, hW''eq, inv_smul_smul]
  refine ⟨vcX D X₁, vcY D X₁ Y₁, hR', hgyR', hΔ'', D⁻¹ * C₀ * D, hC, ?_, fun P => ?_⟩
  ·
    intro x y hxy hgyxy hne
    have hxy₀ : (D • W).toAffine.Equation (vcXInv D x) (vcYInv D x y) :=
      (equation_variableChange_iff _ _).mpr (by rw [vcX_vcXInv, vcY_vcYInv]; exact hxy)
    have hgyxy₀ : (D • W).veluGy (vcXInv D x) (vcYInv D x y) = 0 :=
      variableChange_veluGy_eq_zero D W hgyxy
    have hne₀ : vcXInv D x ≠ vcXInv D x₀ := fun h =>
      hne (by have := congrArg (vcX D) h; simpa using this)
    obtain ⟨hX, hY⟩ := clause₀ _ _ hxy₀ hgyxy₀ hne₀
    rw [variableChange_velu2X_of_veluGy_eq_zero D W hgy hne] at hX
    rw [variableChange_velu2Y_of_veluGy_eq_zero D W hgy hne] at hY
    refine ⟨?_, ?_⟩
    · rw [← hX, vcX_vcXInv]
    · rw [← hY, ← hX, vcY_vcYInv]

  rcases P with _ | ⟨x, y, hns⟩
  ·
    rw [veluPointMap2_zero, veluPointMap2_zero, equivOfVariableChangeEq_zero' hC]
    exact (zsmul_zero (2 : ℤ)).symm
  ·
    have hns₀ : (D • W).toAffine.Nonsingular (vcXInv D x) (vcYInv D x y) :=
      (nonsingular_variableChange_iff _ _).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])
    have key : vcFun D W (equivOfVariableChangeEq hC₀
          (veluPointMap2 h2 hR'₀ hgyR'₀ hΔ₀''
            (veluPointMap2 h2 hQ₀ hgy₀ hΔ₀' (.some (vcXInv D x) (vcYInv D x y) hns₀))))
        = (2 : ℤ) • (.some x y hns) := by
      have hs := seam₀ (vcInvFun D W (.some x y hns))
      rw [← vcInvFun_some D W hns hns₀, hs]
      exact vcFun_two_zsmul_vcInvFun D W _
    rw [← key]; clear key
    by_cases hne₁ : x = x₀
    ·
      have hne₁C : vcXInv D x = vcXInv D x₀ := by rw [hne₁]
      rw [veluPointMap2_some_of_eq h2 hQ hgy hΔ hns hne₁,
        veluPointMap2_some_of_eq h2 hQ₀ hgy₀ hΔ₀' hns₀ hne₁C,
        veluPointMap2_zero, veluPointMap2_zero]
      rw [equivOfVariableChangeEq_zero' hC, equivOfVariableChangeEq_zero' hC₀, vcFun_zero']
    ·
      have hne₁C : vcXInv D x ≠ vcXInv D x₀ := fun h =>
        hne₁ (by have := congrArg (vcX D) h; simpa using this)
      have hnsV := velu2_map_nonsingular h2 hns.1 hQ hgy hne₁ hΔ
      have hnsV₀ := velu2_map_nonsingular h2 hns₀.1 hQ₀ hgy₀ hne₁C hΔ₀'
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hns hne₁,
        veluPointMap2_some_of_ne h2 hQ₀ hgy₀ hΔ₀' hns₀ hne₁C]

      have hxV₀ := variableChange_velu2X_of_veluGy_eq_zero D W hgy hne₁
      have hyV₀ := variableChange_velu2Y_of_veluGy_eq_zero D W hgy hne₁ y
      set xV := W.velu2X x₀ y₀ x
      set yV := W.velu2Y x₀ y₀ x y
      by_cases hne₂ : xV = vcX D X₁
      ·
        have hne₂C : (D • W).velu2X (vcXInv D x₀) (vcYInv D x₀ y₀) (vcXInv D x) = X₁ := by
          rw [hxV₀, hne₂, vcXInv_vcX]
        rw [veluPointMap2_some_of_eq h2 hR' hgyR' hΔ'' hnsV hne₂,
          veluPointMap2_some_of_eq h2 hR'₀ hgyR'₀ hΔ₀'' hnsV₀ hne₂C]
        rw [equivOfVariableChangeEq_zero' hC, equivOfVariableChangeEq_zero' hC₀, vcFun_zero']
      ·
        have hne₂C :
            (D • W).velu2X (vcXInv D x₀) (vcYInv D x₀ y₀) (vcXInv D x) ≠ X₁ := by
          rw [hxV₀]; intro h
          exact hne₂ (by have := congrArg (vcX D) h; simpa using this)
        have hnsVV := velu2_map_nonsingular h2 hnsV.1 hR' hgyR' hne₂ hΔ''
        have hnsVV₀ := velu2_map_nonsingular h2 hnsV₀.1 hR'₀ hgyR'₀ hne₂C hΔ₀''
        rw [veluPointMap2_some_of_ne h2 hR' hgyR' hΔ'' hnsV hne₂,
          veluPointMap2_some_of_ne h2 hR'₀ hgyR'₀ hΔ₀'' hnsV₀ hne₂C]
        set xVV₀ := ((D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)).velu2X X₁ Y₁
            ((D • W).velu2X (vcXInv D x₀) (vcYInv D x₀ y₀) (vcXInv D x)) with hxVV₀_def
        set yVV₀ := ((D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)).velu2Y X₁ Y₁
            ((D • W).velu2X (vcXInv D x₀) (vcYInv D x₀ y₀) (vcXInv D x))
            ((D • W).velu2Y (vcXInv D x₀) (vcYInv D x₀ y₀) (vcXInv D x) (vcYInv D x y))
          with hyVV₀_def

        have huD : (D.u : K) ≠ 0 := D.u.ne_zero
        have hdV : xV - vcX D X₁ ≠ 0 := sub_ne_zero.mpr hne₂
        have hden₁ : vcXInv D xV - X₁ = ((D.u⁻¹ : Kˣ) : K) ^ 2 * (xV - vcX D X₁) := by
          conv_lhs => rw [show X₁ = vcXInv D (vcX D X₁) from (vcXInv_vcX X₁).symm]
          exact vcXInv_sub_vcXInv D _ _
        have hgx₁ :
            ((D • W).veluQuotient2 (vcXInv D x₀) (vcYInv D x₀ y₀)).veluGx X₁ Y₁
              = ((D.u⁻¹ : Kˣ) : K) ^ 4
                * (W.veluQuotient2 x₀ y₀).veluGx (vcX D X₁) (vcY D X₁ Y₁) := by
          conv_lhs => rw [hW'eq, show X₁ = vcXInv D (vcX D X₁) from (vcXInv_vcX X₁).symm,
            show Y₁ = vcYInv D (vcX D X₁) (vcY D X₁ Y₁) from (vcYInv_vcY X₁ Y₁).symm]
          exact variableChange_veluGx_of_veluGy_eq_zero D _ hgyR'
        have hxVV₀ : xVV₀ = vcXInv D ((W.veluQuotient2 x₀ y₀).velu2X
            (vcX D X₁) (vcY D X₁ Y₁) xV) := by
          rw [hxVV₀_def, hxV₀, velu2X, velu2X, hgx₁, hden₁]
          simp only [vcXInv, Units.val_inv_eq_inv_val]
          field_simp; ring
        have hyVV₀ : yVV₀ = vcYInv D
            ((W.veluQuotient2 x₀ y₀).velu2X (vcX D X₁) (vcY D X₁ Y₁) xV)
            ((W.veluQuotient2 x₀ y₀).velu2Y (vcX D X₁) (vcY D X₁ Y₁) xV yV) := by
          rw [hyVV₀_def, hxV₀, hyV₀]
          conv_lhs => rw [hW'eq,
            show X₁ = vcXInv D (vcX D X₁) from (vcXInv_vcX X₁).symm,
            show Y₁ = vcYInv D (vcX D X₁) (vcY D X₁ Y₁) from (vcYInv_vcY X₁ Y₁).symm]
          exact variableChange_velu2Y_of_veluGy_eq_zero D _ hgyR' hne₂ _
        clear hxVV₀_def hyVV₀_def

        have hns₀W := nonsingular_vc_of_eq hC₀ hnsVV₀
        have hnsW₀ : W.toAffine.Nonsingular (vcX D (vcX C₀ xVV₀))
            (vcY D (vcX C₀ xVV₀) (vcY C₀ xVV₀ yVV₀)) :=
          (nonsingular_variableChange_iff _ _).mp hns₀W
        rw [equivOfVariableChangeEq_some hC₀ hnsVV₀ hns₀W, vcFun_some D W hns₀W hnsW₀]

        have hnsW := nonsingular_vc_of_eq hC hnsVV
        rw [equivOfVariableChangeEq_some hC hnsVV hnsW]

        refine some_ext ?_ ?_
        · rw [vcX_conj, hxVV₀]
        · rw [vcY_conj, hxVV₀, hyVV₀]

end S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero (solution)
