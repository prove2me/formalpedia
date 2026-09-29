-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9913febc-f184-574a-87ce-42f4fe4e265e

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VeluOrderTwoShortNF
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option Elab.async false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace VeluTwoDual

section PointHelpers

variable {F : Type*} [Field F] [DecidableEq F]

lemma nonsingular_vc_of_eq {C : VariableChange F} {W V : Affine F} (h : C • W = V) {x y : F}
    (hns : V.Nonsingular x y) : W.Nonsingular (vcX C x) (vcY C x y) := by
  subst h; exact (nonsingular_variableChange_iff x y).mp hns

lemma equivOfVariableChangeEq_zero {C : VariableChange F} {W V : Affine F} (h : C • W = V) :
    equivOfVariableChangeEq h (0 : V.Point) = 0 := by
  subst h; rfl

lemma equivOfVariableChangeEq_zero' {C : VariableChange F} {W V : Affine F} (h : C • W = V) :
    equivOfVariableChangeEq h (.zero : V.Point) = .zero := by
  subst h; rfl

lemma vcFun_zero' (C : VariableChange F) (W : Affine F) :
    vcFun C W (.zero : (C • W).toAffine.Point) = .zero := rfl

lemma equivOfVariableChangeEq_some {C : VariableChange F} {W V : Affine F} (h : C • W = V)
    {x y : F} (hns : V.Nonsingular x y) (hns' : W.Nonsingular (vcX C x) (vcY C x y)) :
    equivOfVariableChangeEq h (.some x y hns) = .some (vcX C x) (vcY C x y) hns' := by
  subst h; rfl

lemma vcFun_some (C : VariableChange F) (W : Affine F) {x y : F}
    (hns : (C • W).toAffine.Nonsingular x y) (hns' : W.Nonsingular (vcX C x) (vcY C x y)) :
    vcFun C W (.some x y hns) = .some (vcX C x) (vcY C x y) hns' := rfl

lemma vcInvFun_some (C : VariableChange F) (W : Affine F) {x y : F}
    (hns : W.Nonsingular x y) (hns' : (C • W).toAffine.Nonsingular (vcXInv C x) (vcYInv C x y)) :
    vcInvFun C W (.some x y hns) = .some (vcXInv C x) (vcYInv C x y) hns' := rfl

noncomputable def vcInvHom (C : VariableChange F) (W : Affine F) :
    W.Point →+ (C • W).toAffine.Point where
  toFun := vcInvFun C W
  map_zero' := rfl
  map_add' := vcInvFun_add C W

lemma vcInvHom_apply (C : VariableChange F) (W : Affine F) (P : W.Point) :
    vcInvHom C W P = vcInvFun C W P := rfl

lemma vcFun_two_zsmul_vcInvFun (C : VariableChange F) (W : Affine F) (P : W.Point) :
    vcFun C W ((2 : ℤ) • vcInvFun C W P) = (2 : ℤ) • P := by
  have h : (2 : ℤ) • vcInvFun C W P = vcInvFun C W ((2 : ℤ) • P) := by
    rw [← vcInvHom_apply, ← vcInvHom_apply, map_zsmul]
  rw [h]
  exact vcFun_rightInverse ((2 : ℤ) • P)

lemma some_ext {W' : Affine F} {x₁ x₂ y₁ y₂ : F} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

omit [DecidableEq F] in

lemma eq_negY_of_veluGy_eq_zero {W : WeierstrassCurve F} {x y : F} (h : W.veluGy x y = 0) :
    y = W.toAffine.negY x y := by
  rw [veluGy, neg_eq_zero] at h
  rw [Affine.negY]
  linear_combination h

omit [DecidableEq F] in

lemma negY_of_isShortNF {W : WeierstrassCurve F} [W.IsShortNF] (x y : F) :
    W.toAffine.negY x y = -y := by
  rw [Affine.negY, a₁_of_isShortNF, a₃_of_isShortNF]
  ring

theorem two_zsmul_some_zero_eq_zero_of_isShortNF {W : WeierstrassCurve F} [W.IsShortNF] {e : F}
    (h : W.toAffine.Nonsingular e 0) : (2 : ℤ) • (Point.some e 0 h : W.toAffine.Point) = 0 := by
  rw [two_zsmul]
  apply add_self_of_Y_eq
  rw [negY_of_isShortNF]
  exact _root_.neg_zero.symm

end PointHelpers

section ShortNFHelpers

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsShortNF]
variable {e : F} (he : e ^ 3 + W.a₄ * e + W.a₆ = 0)

include he in

theorem neg_two_e_root_of_quotient :
    (-2 * e) ^ 3 + (W.veluQuotient2 e 0).a₄ * (-2 * e) + (W.veluQuotient2 e 0).a₆ = 0 := by
  rw [veluQuotient2_a₄_of_isShortNF, veluQuotient2_a₆_of_isShortNF]
  linear_combination he

include he in

theorem other_roots_quadratic_factorization (x : F) :
    (x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄) = x ^ 3 + W.a₄ * x + W.a₆ := by
  linear_combination -he

include he in

theorem other_roots_quadratic_eq_zero {f : F} (hf : f ^ 3 + W.a₄ * f + W.a₆ = 0)
    (hne : f ≠ e) : f ^ 2 + e * f + e ^ 2 + W.a₄ = 0 := by
  have hd : f - e ≠ 0 := sub_ne_zero.mpr hne
  have key : (f - e) * (f ^ 2 + e * f + e ^ 2 + W.a₄) = 0 := by
    rw [other_roots_quadratic_factorization W he]; exact hf
  exact (mul_eq_zero.mp key).resolve_left hd

include he in

theorem velu2X_other_root_eq_neg_two_e {f : F} (hf : f ^ 3 + W.a₄ * f + W.a₆ = 0)
    (hne : f ≠ e) : W.velu2X e 0 f = -2 * e := by
  have hd : f - e ≠ 0 := sub_ne_zero.mpr hne
  have hQ0 := other_roots_quadratic_eq_zero W he hf hne
  rw [velu2X, veluGx_of_isShortNF]
  field_simp
  linear_combination hQ0

theorem velu2Y_zero_of_isShortNF (x₀ x : F) : W.velu2Y x₀ 0 x 0 = 0 := by
  simp only [velu2Y, a₁_of_isShortNF, zero_mul, zero_add, mul_zero, zero_div, sub_zero]

theorem doubleQuotient_a₄ :
    ((W.veluQuotient2 e 0).veluQuotient2 (-2 * e) 0).a₄ = 16 * W.a₄ := by
  rw [veluQuotient2_a₄_of_isShortNF, veluQuotient2_a₄_of_isShortNF]
  ring

include he in

theorem doubleQuotient_a₆ :
    ((W.veluQuotient2 e 0).veluQuotient2 (-2 * e) 0).a₆ = 64 * W.a₆ := by
  rw [veluQuotient2_a₆_of_isShortNF, veluQuotient2_a₆_of_isShortNF,
    veluQuotient2_a₄_of_isShortNF]
  linear_combination -63 * he

def scalingHalf (h2 : (2 : F) ≠ 0) : VariableChange F := ⟨(Units.mk0 2 h2)⁻¹, 0, 0, 0⟩

lemma scalingHalf_u (h2 : (2 : F) ≠ 0) : (((scalingHalf h2).u : Fˣ) : F) = 2⁻¹ := by
  simp only [scalingHalf, Units.val_inv_eq_inv_val, Units.val_mk0]

lemma scalingHalf_u_inv (h2 : (2 : F) ≠ 0) : (((scalingHalf h2).u⁻¹ : Fˣ) : F) = 2 := by
  simp only [scalingHalf, inv_inv, Units.val_mk0]

include he in

theorem smul_eq_doubleQuotient (h2 : (2 : F) ≠ 0) :
    (scalingHalf h2) • W = (W.veluQuotient2 e 0).veluQuotient2 (-2 * e) 0 := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, scalingHalf, inv_inv, Units.val_mk0,
    veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃, a₁_of_isShortNF, a₂_of_isShortNF,
    a₃_of_isShortNF, doubleQuotient_a₄, doubleQuotient_a₆ W he, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add] <;> ring

theorem velu2X_plus_two_e {x : F} (hne : x ≠ e) :
    W.velu2X e 0 x + 2 * e = (x ^ 2 + e * x + e ^ 2 + W.a₄) / (x - e) := by
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, veluGx_of_isShortNF]; field_simp; ring

end ShortNFHelpers

section SeamIdentities

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.IsShortNF]
variable {e x y : F} (he : e ^ 3 + W.a₄ * e + W.a₆ = 0)
  (hP : y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆) (hy : y ≠ 0)

include he hP hy in

theorem ne_e_of_y_ne_zero : x ≠ e := by
  intro hxe; subst hxe
  exact hy (pow_eq_zero_iff two_ne_zero |>.mp (hP.trans he))

include he hP hy in

theorem other_roots_quadratic_ne_zero : x ^ 2 + e * x + e ^ 2 + W.a₄ ≠ 0 := by
  intro hQ
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hy2 : y ^ 2 = 0 := by
    rw [hP, ← other_roots_quadratic_factorization W he, hQ, mul_zero]
  exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)

include he hP hy in

theorem velu2X_ne_neg_two_e : W.velu2X e 0 x ≠ -2 * e := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hQne : x ^ 2 + e * x + e ^ 2 + W.a₄ ≠ 0 := other_roots_quadratic_ne_zero W he hP hy
  intro heq
  have h := velu2X_plus_two_e W hxe
  have h0 : (x ^ 2 + e * x + e ^ 2 + W.a₄) / (x - e) = 0 := by
    rw [← h, heq]; ring
  exact hQne ((div_eq_zero_iff.mp h0).resolve_right hd)

omit [DecidableEq F] in

lemma eq_zero_of_eq_neg (h2 : (2 : F) ≠ 0) {z : F} (h : z = -z) : z = 0 := by
  have : (2 : F) * z = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

omit [DecidableEq F] in

lemma vcX_scalingHalf (h2 : (2 : F) ≠ 0) (z : F) :
    vcX (scalingHalf h2) z = (2 : F)⁻¹ ^ 2 * z := by
  simp only [vcX, scalingHalf, Units.val_inv_eq_inv_val, Units.val_mk0, add_zero]

omit [DecidableEq F] in

lemma vcY_scalingHalf (h2 : (2 : F) ≠ 0) (z w : F) :
    vcY (scalingHalf h2) z w = (2 : F)⁻¹ ^ 3 * w := by
  simp only [vcY, scalingHalf, Units.val_inv_eq_inv_val, Units.val_mk0, add_zero, mul_zero,
    zero_mul]

theorem velu2X_mul_sub {x : F} (hne : x ≠ e) :
    W.velu2X e 0 x * (x - e) = x * (x - e) + (3 * e ^ 2 + W.a₄) := by
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, veluGx_of_isShortNF]; field_simp

theorem velu2X_sub_neg_two_e_mul_sub {x : F} (hne : x ≠ e) :
    (W.velu2X e 0 x - -2 * e) * (x - e) = x ^ 2 + e * x + e ^ 2 + W.a₄ := by
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, veluGx_of_isShortNF]; field_simp; ring

include he hP in

theorem doubleQuot_xCoord_cleared :
    y ^ 2 * ((x ^ 2 + e * x + e ^ 2 + W.a₄) * (x * (x - e) + (3 * e ^ 2 + W.a₄))
        + (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2)
      = (x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄)
        * ((3 * x ^ 2 + W.a₄) ^ 2 - 8 * x * y ^ 2) := by
  linear_combination (3 * x ^ 2 + W.a₄) ^ 2 * hP + (3 * x ^ 2 + W.a₄) ^ 2 * he

include he hP hy in

theorem doubleQuot_xCoord_eq (h2 : (2 : F) ≠ 0) :
    vcX (scalingHalf h2)
        ((W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x))
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hQne : x ^ 2 + e * x + e ^ 2 + W.a₄ ≠ 0 := other_roots_quadratic_ne_zero W he hP hy
  have hYne : y ≠ W.toAffine.negY x y := by
    rw [negY_of_isShortNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)
  have hX1p_ne : W.velu2X e 0 x - -2 * e ≠ 0 := fun h => hQne (by
    rw [← velu2X_sub_neg_two_e_mul_sub W hxe, h, zero_mul])
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy

  have step : (W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x)
        * (W.velu2X e 0 x - -2 * e)
      = W.velu2X e 0 x * (W.velu2X e 0 x - -2 * e) + (-(3 * e ^ 2 + 4 * W.a₄)) := by
    conv_lhs => rw [velu2X, veluGx_of_isShortNF, veluQuotient2_a₄_of_isShortNF, add_mul,
      div_mul_cancel₀ _ hX1p_ne]
    ring

  have hX2_clear : (W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x)
        * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄))
      = (x ^ 2 + e * x + e ^ 2 + W.a₄) * (x * (x - e) + (3 * e ^ 2 + W.a₄))
        + (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2 := by
    have h1 : (W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x)
          * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄))
        = (W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x)
          * (W.velu2X e 0 x - -2 * e) * (x - e) ^ 2 := by
      rw [← velu2X_sub_neg_two_e_mul_sub W hxe]; ring
    rw [h1, step, add_mul,
      show W.velu2X e 0 x * (W.velu2X e 0 x - -2 * e) * (x - e) ^ 2
        = (W.velu2X e 0 x * (x - e)) * ((W.velu2X e 0 x - -2 * e) * (x - e)) from by ring,
      velu2X_mul_sub W hxe, velu2X_sub_neg_two_e_mul_sub W hxe]
    ring

  have haddX_clear : (2 * y) ^ 2 * W.toAffine.addX x x (W.toAffine.slope x x y y)
      = (3 * x ^ 2 + W.a₄) ^ 2 - 8 * x * y ^ 2 := by
    rw [slope_of_Y_ne rfl hYne, addX, a₁_of_isShortNF, a₂_of_isShortNF, negY_of_isShortNF,
      show y - -y = 2 * y from by ring]
    field_simp
    ring

  have hdenom : (2 * y) ^ 2 * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (mul_ne_zero h2 hy)) (mul_ne_zero hd hQne)
  have hscale : ((2 : F) * (2 : F)⁻¹) ^ 2 = 1 := by rw [mul_inv_cancel₀ h2, one_pow]
  refine mul_left_cancel₀ hdenom ?_
  rw [vcX_scalingHalf h2]
  calc (2 * y) ^ 2 * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄))
          * ((2 : F)⁻¹ ^ 2 * (W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x))
      = ((2 : F) * (2 : F)⁻¹) ^ 2 * (y ^ 2 * ((W.veluQuotient2 e 0).velu2X (-2 * e) 0
          (W.velu2X e 0 x) * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄)))) := by ring
    _ = y ^ 2 * ((W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x)
          * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄))) := by rw [hscale, one_mul]
    _ = y ^ 2 * ((x ^ 2 + e * x + e ^ 2 + W.a₄) * (x * (x - e) + (3 * e ^ 2 + W.a₄))
          + (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2) := by rw [hX2_clear]
    _ = (x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄)
          * ((3 * x ^ 2 + W.a₄) ^ 2 - 8 * x * y ^ 2) := doubleQuot_xCoord_cleared W he hP
    _ = (2 * y) ^ 2 * ((x - e) * (x ^ 2 + e * x + e ^ 2 + W.a₄))
          * W.toAffine.addX x x (W.toAffine.slope x x y y) := by rw [← haddX_clear]; ring

set_option maxHeartbeats 3200000 in
include he hP in

theorem doubleQuot_yCoord_cleared :
    y ^ 3 * (y * ((x - e) ^ 2 - (3 * e ^ 2 + W.a₄))
        * ((x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2 - (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2))
      = (x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2
        * (-(3 * x ^ 2 + W.a₄) ^ 3 + 12 * x * y ^ 2 * (3 * x ^ 2 + W.a₄) - 8 * y ^ 4) := by
  linear_combination
    (-W.a₄ ^ 4 * x - W.a₄ ^ 3 * W.a₆ - 12 * W.a₄ ^ 3 * e ^ 2 * x + 12 * W.a₄ ^ 3 * e * x ^ 2
     - 10 * W.a₄ ^ 3 * x ^ 3 - W.a₄ ^ 3 * y ^ 2 - 12 * W.a₄ ^ 2 * W.a₆ * e * x
     + 3 * W.a₄ ^ 2 * W.a₆ * x ^ 2 - 24 * W.a₄ ^ 2 * e ^ 4 * x + 12 * W.a₄ ^ 2 * e ^ 3 * x ^ 2
     - 36 * W.a₄ ^ 2 * e ^ 2 * x ^ 3 + 48 * W.a₄ ^ 2 * e * x ^ 4 - 12 * W.a₄ ^ 2 * e * x * y ^ 2
     - 36 * W.a₄ ^ 2 * x ^ 5 + 3 * W.a₄ ^ 2 * x ^ 2 * y ^ 2 - 12 * W.a₄ * W.a₆ * e ^ 3 * x
     - 36 * W.a₄ * W.a₆ * e * x ^ 3 + 21 * W.a₄ * W.a₆ * x ^ 4 - 12 * W.a₄ * e ^ 6 * x
     - 72 * W.a₄ * e ^ 4 * x ^ 3 + 48 * W.a₄ * e ^ 3 * x ^ 4 - 12 * W.a₄ * e ^ 3 * x * y ^ 2
     + 36 * W.a₄ * e * x ^ 6 - 36 * W.a₄ * e * x ^ 3 * y ^ 2 - 54 * W.a₄ * x ^ 7
     + 21 * W.a₄ * x ^ 4 * y ^ 2 - 36 * W.a₆ * e ^ 3 * x ^ 3 + 9 * W.a₆ * x ^ 6
     - 36 * e ^ 6 * x ^ 3 + 36 * e ^ 3 * x ^ 6 - 36 * e ^ 3 * x ^ 3 * y ^ 2 - 27 * x ^ 9
     + 9 * x ^ 6 * y ^ 2) * hP
    + (W.a₄ ^ 4 * e - 2 * W.a₄ ^ 4 * x - W.a₄ ^ 3 * W.a₆ + W.a₄ ^ 3 * e ^ 3
     - 3 * W.a₄ ^ 3 * e * x ^ 2 - 8 * W.a₄ ^ 3 * x ^ 3 - 12 * W.a₄ ^ 2 * W.a₆ * e * x
     + 3 * W.a₄ ^ 2 * W.a₆ * x ^ 2 - 3 * W.a₄ ^ 2 * e ^ 3 * x ^ 2 - 21 * W.a₄ ^ 2 * e * x ^ 4
     - 12 * W.a₄ ^ 2 * x ^ 5 - 12 * W.a₄ * W.a₆ * e ^ 3 * x - 36 * W.a₄ * W.a₆ * e * x ^ 3
     + 21 * W.a₄ * W.a₆ * x ^ 4 - 21 * W.a₄ * e ^ 3 * x ^ 4 - 9 * W.a₄ * e * x ^ 6
     - 24 * W.a₄ * x ^ 7 - 36 * W.a₆ * e ^ 3 * x ^ 3 + 9 * W.a₆ * x ^ 6 - 9 * e ^ 3 * x ^ 6
     - 18 * x ^ 9) * he

include he hP hy in

theorem doubleQuot_yCoord_eq (h2 : (2 : F) ≠ 0) :
    vcY (scalingHalf h2)
        ((W.veluQuotient2 e 0).velu2X (-2 * e) 0 (W.velu2X e 0 x))
        ((W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y))
      = W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
  have hxe : x ≠ e := ne_e_of_y_ne_zero W he hP hy
  have hd : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hQne : x ^ 2 + e * x + e ^ 2 + W.a₄ ≠ 0 := other_roots_quadratic_ne_zero W he hP hy
  have hYne : y ≠ W.toAffine.negY x y := by
    rw [negY_of_isShortNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)
  have hX1p_ne : W.velu2X e 0 x - -2 * e ≠ 0 := fun h => hQne (by
    rw [← velu2X_sub_neg_two_e_mul_sub W hxe, h, zero_mul])
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero h2 hy

  have hY1_clear : W.velu2Y e 0 x y * (x - e) ^ 2 = y * ((x - e) ^ 2 - (3 * e ^ 2 + W.a₄)) := by
    rw [velu2Y, veluGx_of_isShortNF, a₁_of_isShortNF]; field_simp; ring

  have stepY : (W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
        * (W.velu2X e 0 x - -2 * e) ^ 2
      = W.velu2Y e 0 x y * ((W.velu2X e 0 x - -2 * e) ^ 2 - (-(3 * e ^ 2 + 4 * W.a₄))) := by
    conv_lhs => rw [velu2Y, veluGx_of_isShortNF, veluQuotient2_a₄_of_isShortNF,
      veluQuotient2_a₁, a₁_of_isShortNF, zero_mul, zero_add, sub_zero, sub_mul,
      mul_div_assoc, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hX1p_ne)]
    ring

  have hY2_clear : (W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
        * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2)
      = y * ((x - e) ^ 2 - (3 * e ^ 2 + W.a₄))
        * ((x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2 - (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2) := by
    have h1 : (W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
          * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2)
        = (W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
          * (W.velu2X e 0 x - -2 * e) ^ 2 * (x - e) ^ 4 := by
      rw [← velu2X_sub_neg_two_e_mul_sub W hxe]; ring
    rw [h1, stepY]
    have h2sq : ((W.velu2X e 0 x - -2 * e) * (x - e)) ^ 2 = (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2 :=
      by rw [velu2X_sub_neg_two_e_mul_sub W hxe]
    calc W.velu2Y e 0 x y * ((W.velu2X e 0 x - -2 * e) ^ 2 - (-(3 * e ^ 2 + 4 * W.a₄)))
            * (x - e) ^ 4
        = (W.velu2Y e 0 x y * (x - e) ^ 2)
            * (((W.velu2X e 0 x - -2 * e) * (x - e)) ^ 2
              - (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2) := by ring
      _ = y * ((x - e) ^ 2 - (3 * e ^ 2 + W.a₄))
            * ((x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2
              - (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2) := by rw [hY1_clear, h2sq]

  have haddY_clear : (2 * y) ^ 3 * W.toAffine.addY x x y (W.toAffine.slope x x y y)
      = -(3 * x ^ 2 + W.a₄) ^ 3 + 12 * x * y ^ 2 * (3 * x ^ 2 + W.a₄) - 8 * y ^ 4 := by
    rw [slope_of_Y_ne rfl hYne, addY, negAddY, addX, negY, a₁_of_isShortNF, a₂_of_isShortNF,
      a₃_of_isShortNF, negY_of_isShortNF, show y - -y = 2 * y from by ring]
    field_simp
    ring

  have hdenom : (2 * y) ^ 3 * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 (mul_ne_zero h2 hy))
      (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 2 hQne))
  refine mul_left_cancel₀ hdenom ?_
  rw [vcY_scalingHalf h2]
  calc (2 * y) ^ 3 * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2)
          * ((2 : F)⁻¹ ^ 3
            * (W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y))
      = y ^ 3 * ((W.veluQuotient2 e 0).velu2Y (-2 * e) 0 (W.velu2X e 0 x) (W.velu2Y e 0 x y)
          * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2)) := by
        have hscale : ((2 : F) * (2 : F)⁻¹) ^ 3 = 1 := by rw [mul_inv_cancel₀ h2, one_pow]
        calc _ = ((2 : F) * (2 : F)⁻¹) ^ 3 * (y ^ 3 * ((W.veluQuotient2 e 0).velu2Y (-2 * e) 0
                (W.velu2X e 0 x) (W.velu2Y e 0 x y)
              * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2))) := by ring
          _ = _ := by rw [hscale, one_mul]
    _ = y ^ 3 * (y * ((x - e) ^ 2 - (3 * e ^ 2 + W.a₄))
          * ((x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2
            - (-(3 * e ^ 2 + 4 * W.a₄)) * (x - e) ^ 2)) := by rw [hY2_clear]
    _ = (x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2
          * (-(3 * x ^ 2 + W.a₄) ^ 3 + 12 * x * y ^ 2 * (3 * x ^ 2 + W.a₄) - 8 * y ^ 4) :=
        doubleQuot_yCoord_cleared W he hP
    _ = (2 * y) ^ 3 * ((x - e) ^ 2 * (x ^ 2 + e * x + e ^ 2 + W.a₄) ^ 2)
          * W.toAffine.addY x x y (W.toAffine.slope x x y y) := by rw [← haddY_clear]; ring

end SeamIdentities

section ShortNFCore

variable {F : Type*} [Field F] [DecidableEq F]

theorem core (h2 : (2 : F) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF] {x₀ y₀ : F}
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

  obtain rfl : y₀ = 0 := by
    have h := hgy
    simp only [veluGy, a₁_of_isShortNF, a₃_of_isShortNF, add_zero, zero_mul, neg_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left h2

  have he : x₀ ^ 3 + W.a₄ * x₀ + W.a₆ = 0 := (equation_zero_iff_of_isShortNF W x₀).mp hQ

  have hR' : (W.veluQuotient2 x₀ 0).toAffine.Equation (-2 * x₀) 0 :=
    (equation_zero_iff_of_isShortNF _ _).mpr (neg_two_e_root_of_quotient W he)
  have hgyR' : (W.veluQuotient2 x₀ 0).veluGy (-2 * x₀) 0 = 0 := veluGy_zero_of_isShortNF _ _
  have hC : (scalingHalf h2) • W = (W.veluQuotient2 x₀ 0).veluQuotient2 (-2 * x₀) 0 :=
    smul_eq_doubleQuotient W he h2
  have hΔ'' : ((W.veluQuotient2 x₀ 0).veluQuotient2 (-2 * x₀) 0).Δ ≠ 0 := by
    rw [← hC, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) W.isUnit_Δ.ne_zero
  refine ⟨-2 * x₀, 0, hR', hgyR', hΔ'', scalingHalf h2, hC, ?_, fun P => ?_⟩
  ·
    intro x y hxy hgyxy hne
    obtain rfl : y = 0 := by
      have h := hgyxy
      simp only [veluGy, a₁_of_isShortNF, a₃_of_isShortNF, add_zero, zero_mul, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    have hx_root : x ^ 3 + W.a₄ * x + W.a₆ = 0 := (equation_zero_iff_of_isShortNF W x).mp hxy
    exact ⟨velu2X_other_root_eq_neg_two_e W he hx_root hne, velu2Y_zero_of_isShortNF W x₀ x⟩

  rcases P with _ | ⟨x, y, hns⟩
  ·
    rw [veluPointMap2_zero, veluPointMap2_zero, equivOfVariableChangeEq_zero' hC]
    exact (zsmul_zero (2 : ℤ)).symm
  ·
    have hPeq : y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
      have heq := (Affine.equation_iff x y).mp hns.1
      linear_combination heq + x ^ 2 * a₂_of_isShortNF W - x * y * a₁_of_isShortNF W
        - y * a₃_of_isShortNF W
    by_cases hy : y = 0
    ·
      subst hy
      rw [two_zsmul_some_zero_eq_zero_of_isShortNF hns]
      by_cases hxe : x = x₀
      ·
        rw [veluPointMap2_some_of_eq h2 hQ hgy hΔ hns hxe, veluPointMap2_zero]
        exact equivOfVariableChangeEq_zero hC
      ·
        have hx_root : x ^ 3 + W.a₄ * x + W.a₆ = 0 := by linear_combination -hPeq
        have hX1 : W.velu2X x₀ 0 x = -2 * x₀ :=
          velu2X_other_root_eq_neg_two_e W he hx_root hxe
        have hnsQ' := velu2_map_nonsingular h2 hns.1 hQ hgy hxe hΔ
        rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hns hxe,
          veluPointMap2_some_of_eq h2 hR' hgyR' hΔ'' hnsQ' hX1]
        exact equivOfVariableChangeEq_zero hC
    ·
      have hxe : x ≠ x₀ := ne_e_of_y_ne_zero W he hPeq hy
      have hX1_ne : W.velu2X x₀ 0 x ≠ -2 * x₀ := velu2X_ne_neg_two_e W he hPeq hy
      have hYne : y ≠ W.toAffine.negY x y := by
        rw [negY_of_isShortNF]; exact fun h => hy (eq_zero_of_eq_neg h2 h)

      rw [two_zsmul, add_self_of_Y_ne hYne]

      have hnsQ' := velu2_map_nonsingular h2 hns.1 hQ hgy hxe hΔ
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ hns hxe,
        veluPointMap2_some_of_ne h2 hR' hgyR' hΔ'' hnsQ' hX1_ne]
      have hnsQ'' := velu2_map_nonsingular h2 hnsQ'.1 hR' hgyR' hX1_ne hΔ''
      have hnsW := nonsingular_vc_of_eq hC hnsQ''
      rw [equivOfVariableChangeEq_some hC hnsQ'' hnsW]
      exact some_ext (doubleQuot_xCoord_eq W he hPeq hy h2) (doubleQuot_yCoord_eq W he hPeq hy h2)

end ShortNFCore

section VCCompat

variable {F : Type*} [Field F]
variable (C : VariableChange F) (W : WeierstrassCurve F) {x₀ y₀ : F}

theorem variableChange_veluGx_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    (C • W).veluGx (vcXInv C x₀) (vcYInv C x₀ y₀)
      = ((C.u⁻¹ : Fˣ) : F) ^ 4 * W.veluGx x₀ y₀ := by
  rw [variableChange_veluGx, hgy, mul_zero, add_zero]

theorem variableChange_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    (C • W).veluGy (vcXInv C x₀) (vcYInv C x₀ y₀) = 0 := by
  rw [variableChange_veluGy, hgy, mul_zero]

theorem variableChange_veluQuotient2_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
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
  · simp only [veluQuotient2_a₆, veluQuotient2_a₄, veluQuotient2_a₁, veluQuotient2_a₂,
      veluQuotient2_a₃, hgx]
    simp only [variableChange_a₆, variableChange_a₁, variableChange_a₂, veluQuotient2_a₁,
      veluQuotient2_a₂, veluQuotient2_a₃, veluQuotient2_a₄, veluQuotient2_a₆, b₂, vcXInv,
      Units.val_inv_eq_inv_val]
    field_simp; ring

theorem vcXInv_sub_vcXInv (x x₀ : F) :
    vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - x₀) := by
  simp only [vcXInv]; ring

theorem variableChange_velu2X_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) {x : F}
    (hne : x ≠ x₀) :
    (C • W).velu2X (vcXInv C x₀) (vcYInv C x₀ y₀) (vcXInv C x)
      = vcXInv C (W.velu2X x₀ y₀ x) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2X, velu2X, variableChange_veluGx_of_veluGy_eq_zero C W hgy,
    vcXInv_sub_vcXInv]
  simp only [vcXInv, Units.val_inv_eq_inv_val]
  field_simp; ring

theorem variableChange_velu2Y_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) {x : F}
    (hne : x ≠ x₀) (y : F) :
    (C • W).velu2Y (vcXInv C x₀) (vcYInv C x₀ y₀) (vcXInv C x) (vcYInv C x y)
      = vcYInv C (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [velu2Y, velu2Y, velu2X, variableChange_veluGx_of_veluGy_eq_zero C W hgy,
    vcXInv_sub_vcXInv]
  simp only [vcXInv, vcYInv, variableChange_a₁, Units.val_inv_eq_inv_val]
  field_simp; ring

end VCCompat

section Conj

variable {F : Type*} [Field F]

theorem vcX_conj (D C₀ : VariableChange F) (z : F) :
    vcX (D⁻¹ * C₀ * D) z = vcX D (vcX C₀ (vcXInv D z)) := by
  have huD : (D.u : F) ≠ 0 := D.u.ne_zero
  have huC : (C₀.u : F) ≠ 0 := C₀.u.ne_zero
  simp only [vcX, vcXInv, VariableChange.mul_def, VariableChange.inv_def,
    Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp; ring

theorem vcY_conj (D C₀ : VariableChange F) (z w : F) :
    vcY (D⁻¹ * C₀ * D) z w
      = vcY D (vcX C₀ (vcXInv D z)) (vcY C₀ (vcXInv D z) (vcYInv D z w)) := by
  have huD : (D.u : F) ≠ 0 := D.u.ne_zero
  have huC : (C₀.u : F) ≠ 0 := C₀.u.ne_zero
  simp only [vcX, vcY, vcXInv, vcYInv, VariableChange.mul_def, VariableChange.inv_def,
    Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp; ring

end Conj

end VeluTwoDual

open VeluTwoDual in

theorem solution
    {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
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
  letI : Invertible (3 : K) := invertibleOfNonzero h3
  set D := W.toShortNF with hD_def

  haveI hE₀ : (D • W).IsElliptic := inferInstance
  haveI hSNF₀ : (D • W).IsShortNF := hD_def ▸ W.toShortNF_spec
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

end S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul (solution)
