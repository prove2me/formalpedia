-- Prove2me | solution 1 for WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/235eb75d-5e81-5f94-926a-8a8a3fab3824

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.Equation Affine.negY Affine.evalEval_polynomial Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne VariableChange.map Affine.Point.add_of_Y_eq map variableChange_a₃ Affine.evalEval_polynomialX Affine.Point.some Affine.Point.some.injEq Affine.Nonsingular variableChange_a₆ VariableChange.baseChange Affine.negAddY Affine.slope_of_Y_ne_eq_evalEval variableChange_a₂ toAffine Affine.Point Affine.evalEval_polynomialY Affine.addX Affine.Point.add_some variableChange_a₁ variableChange_a₄ VariableChange Affine.addY Affine.Point.map_some map_variableChange baseChange"
p2m_open "WeierstrassCurve"

namespace VariableChange
p2m_export "WeierstrassCurve.VariableChange" "map u baseChange t s r"
p2m_open "WeierstrassCurve.VariableChange"

section Ring

variable {R : Type*} [CommRing R] (C : VariableChange R) (W : WeierstrassCurve R)

private def _root_.WeierstrassCurve.VariableChange.ptX (x : R) : R := (↑C.u⁻¹ : R) ^ 2 * (x - C.r)

p2m_export "WeierstrassCurve.VariableChange" "ptX"

private def _root_.WeierstrassCurve.VariableChange.ptY (x y : R) : R := (↑C.u⁻¹ : R) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))

p2m_export "WeierstrassCurve.VariableChange" "ptY"

private def _root_.WeierstrassCurve.VariableChange.invX (X : R) : R := (C.u : R) ^ 2 * X + C.r

p2m_export "WeierstrassCurve.VariableChange" "invX"

private def _root_.WeierstrassCurve.VariableChange.invY (X Y : R) : R := (C.u : R) ^ 3 * Y + (C.u : R) ^ 2 * C.s * X + C.t

p2m_export "WeierstrassCurve.VariableChange" "invY"
lemma invX_ptX (x : R) : C.invX (C.ptX x) = x := by
  simp only [invX, ptX]
  linear_combination (x - C.r) * pow_mul_pow_eq_one 2 C.u.mul_inv

lemma invY_ptY (x y : R) : C.invY (C.ptX x) (C.ptY x y) = y := by
  simp only [invY, ptX, ptY]
  linear_combination (y - C.s * x + (C.s * C.r - C.t)) * pow_mul_pow_eq_one 3 C.u.mul_inv
    + C.s * (x - C.r) * pow_mul_pow_eq_one 2 C.u.mul_inv

lemma ptX_invX (X : R) : C.ptX (C.invX X) = X := by
  simp only [invX, ptX]
  linear_combination X * pow_mul_pow_eq_one 2 C.u.inv_mul

lemma ptY_invY (X Y : R) : C.ptY (C.invX X) (C.invY X Y) = Y := by
  simp only [invX, invY, ptY]
  linear_combination Y * pow_mul_pow_eq_one 3 C.u.inv_mul

private lemma _root_.WeierstrassCurve.VariableChange.ptX_injective : Function.Injective C.ptX := fun x₁ x₂ h => by
  simpa only [invX_ptX] using congr_arg C.invX h

p2m_export "WeierstrassCurve.VariableChange" "ptX_injective"
private lemma _root_.WeierstrassCurve.VariableChange.ptY_injective (x : R) : Function.Injective (C.ptY x) := fun y₁ y₂ h => by
  simpa only [invY_ptY] using congr_arg (C.invY (C.ptX x)) h

p2m_export "WeierstrassCurve.VariableChange" "ptY_injective"
lemma negY_pt (x y : R) :
    (C • W).toAffine.negY (C.ptX x) (C.ptY x y) = C.ptY x (W.toAffine.negY x y) := by
  simp only [Affine.negY, ptX, ptY, variableChange_a₁, variableChange_a₃]
  ring

lemma addX_pt (x₁ x₂ ℓ : R) :
    (C • W).toAffine.addX (C.ptX x₁) (C.ptX x₂) (↑C.u⁻¹ * (ℓ - C.s)) =
      C.ptX (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [Affine.addX, ptX, variableChange_a₁, variableChange_a₂]
  ring

lemma addY_pt (x₁ x₂ y₁ ℓ : R) :
    (C • W).toAffine.addY (C.ptX x₁) (C.ptX x₂) (C.ptY x₁ y₁) (↑C.u⁻¹ * (ℓ - C.s)) =
      C.ptY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, ptX, ptY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃]
  ring

lemma evalEval_polynomial_pt (x y : R) :
    (C • W).toAffine.polynomial.evalEval (C.ptX x) (C.ptY x y) =
      ↑C.u⁻¹ ^ 6 * W.toAffine.polynomial.evalEval x y := by
  rw [Affine.evalEval_polynomial, Affine.evalEval_polynomial]
  simp only [ptX, ptY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  ring

lemma evalEval_polynomialX_pt (x y : R) :
    (C • W).toAffine.polynomialX.evalEval (C.ptX x) (C.ptY x y) =
      ↑C.u⁻¹ ^ 4 * (W.toAffine.polynomialX.evalEval x y
        + C.s * W.toAffine.polynomialY.evalEval x y) := by
  rw [Affine.evalEval_polynomialX, Affine.evalEval_polynomialX, Affine.evalEval_polynomialY]
  simp only [ptX, ptY, variableChange_a₁, variableChange_a₂, variableChange_a₄]
  ring

lemma evalEval_polynomialY_pt (x y : R) :
    (C • W).toAffine.polynomialY.evalEval (C.ptX x) (C.ptY x y) =
      ↑C.u⁻¹ ^ 3 * W.toAffine.polynomialY.evalEval x y := by
  rw [Affine.evalEval_polynomialY, Affine.evalEval_polynomialY]
  simp only [ptX, ptY, variableChange_a₁, variableChange_a₃]
  ring

lemma equation_pt_iff (x y : R) :
    (C • W).toAffine.Equation (C.ptX x) (C.ptY x y) ↔ W.toAffine.Equation x y := by
  rw [Affine.Equation, Affine.Equation, evalEval_polynomial_pt,
    (C.u⁻¹.isUnit.pow 6).mul_right_eq_zero]

lemma nonsingular_pt_iff (x y : R) :
    (C • W).toAffine.Nonsingular (C.ptX x) (C.ptY x y) ↔ W.toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, equation_pt_iff, evalEval_polynomialX_pt,
    evalEval_polynomialY_pt]
  simp only [ne_eq, (C.u⁻¹.isUnit.pow 4).mul_right_eq_zero, (C.u⁻¹.isUnit.pow 3).mul_right_eq_zero]
  refine and_congr_right fun _ => ?_
  by_cases hY : W.toAffine.polynomialY.evalEval x y = 0
  · simp only [hY, mul_zero, add_zero, not_true_eq_false, or_false]
  · simp only [hY, not_false_eq_true, or_true]

lemma nonsingular_inv_iff (X Y : R) :
    W.toAffine.Nonsingular (C.invX X) (C.invY X Y) ↔ (C • W).toAffine.Nonsingular X Y := by
  rw [← nonsingular_pt_iff C W, ptX_invX, ptY_invY]

end Ring

section Field

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve K)

lemma slope_pt {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (C.ptX x₁) (C.ptX x₂) (C.ptY x₁ y₁) (C.ptY x₂ y₂) =
      ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hu : (↑C.u⁻¹ : K) ≠ 0 := C.u⁻¹.ne_zero
  have hu' : (↑C.u : K) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    obtain rfl : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst hx
    have hy' : C.ptY x₁ y₁ ≠ (C • W).toAffine.negY (C.ptX x₁) (C.ptY x₁ y₁) := by
      rw [negY_pt]
      exact fun h => hy (C.ptY_injective x₁ h)
    have hB : W.toAffine.polynomialY.evalEval x₁ y₁ ≠ 0 := by
      rw [Affine.evalEval_polynomialY]
      intro h
      apply hy
      simp only [Affine.negY]
      linear_combination h
    rw [Affine.slope_of_Y_ne_eq_evalEval rfl hy', Affine.slope_of_Y_ne_eq_evalEval rfl hy,
      evalEval_polynomialX_pt, evalEval_polynomialY_pt]
    field_simp
    ring
  · have hx' : C.ptX x₁ ≠ C.ptX x₂ := fun h => hx (C.ptX_injective h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hden : C.ptX x₁ - C.ptX x₂ = ↑C.u⁻¹ ^ 2 * (x₁ - x₂) := by simp only [ptX]; ring
    have hnum : C.ptY x₁ y₁ - C.ptY x₂ y₂ = ↑C.u⁻¹ ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      simp only [ptY]; ring
    rw [hden, hnum]
    field_simp

end Field

end VariableChange

section PointEquiv

variable {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K]
  (E : WeierstrassCurve F) (C : VariableChange F)

lemma baseChange_variableChange_smul : (C.baseChange K) • (E⁄K) = (C • E)⁄K :=
  map_variableChange E C (algebraMap F K)

namespace VariableChange
p2m_export "WeierstrassCurve.VariableChange" "map u baseChange t s r"
p2m_open "WeierstrassCurve.VariableChange"

@[scoped simp] lemma coe_baseChange_u_inv : (↑(C.baseChange K).u⁻¹ : K) = algebraMap F K ↑C.u⁻¹ := by
  simp [VariableChange.baseChange, VariableChange.map]

@[scoped simp] lemma baseChange_r : (C.baseChange K).r = algebraMap F K C.r := rfl
@[scoped simp] lemma baseChange_s : (C.baseChange K).s = algebraMap F K C.s := rfl
@[scoped simp] lemma baseChange_t : (C.baseChange K).t = algebraMap F K C.t := rfl

lemma bc_nonsingular_iff (X Y : K) :
    ((C.baseChange K) • (E⁄K)).toAffine.Nonsingular X Y ↔ ((C • E)⁄K).Nonsingular X Y := by
  rw [baseChange_variableChange_smul]

lemma bc_negY (x y : K) :
    ((C • E)⁄K).negY ((C.baseChange K).ptX x) ((C.baseChange K).ptY x y) = (C.baseChange K).ptY x ((E⁄K).negY x y) := by
  rw [← baseChange_variableChange_smul]; exact negY_pt (C.baseChange K) (E⁄K) x y

lemma bc_addX (x₁ x₂ ℓ : K) :
    ((C • E)⁄K).addX ((C.baseChange K).ptX x₁) ((C.baseChange K).ptX x₂) (↑(C.baseChange K).u⁻¹ * (ℓ - (C.baseChange K).s)) =
      (C.baseChange K).ptX ((E⁄K).addX x₁ x₂ ℓ) := by
  rw [← baseChange_variableChange_smul]; exact addX_pt (C.baseChange K) (E⁄K) x₁ x₂ ℓ

lemma bc_addY (x₁ x₂ y₁ ℓ : K) :
    ((C • E)⁄K).addY ((C.baseChange K).ptX x₁) ((C.baseChange K).ptX x₂) ((C.baseChange K).ptY x₁ y₁)
        (↑(C.baseChange K).u⁻¹ * (ℓ - (C.baseChange K).s)) =
      (C.baseChange K).ptY ((E⁄K).addX x₁ x₂ ℓ) ((E⁄K).addY x₁ x₂ y₁ ℓ) := by
  rw [← baseChange_variableChange_smul]; exact addY_pt (C.baseChange K) (E⁄K) x₁ x₂ y₁ ℓ

lemma bc_slope [DecidableEq K] {x₁ x₂ y₁ y₂ : K} (h₁ : (E⁄K).Equation x₁ y₁)
    (h₂ : (E⁄K).Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (E⁄K).negY x₂ y₂)) :
    ((C • E)⁄K).slope ((C.baseChange K).ptX x₁) ((C.baseChange K).ptX x₂) ((C.baseChange K).ptY x₁ y₁) ((C.baseChange K).ptY x₂ y₂) =
      ↑(C.baseChange K).u⁻¹ * ((E⁄K).slope x₁ x₂ y₁ y₂ - (C.baseChange K).s) := by
  rw [← baseChange_variableChange_smul]; exact slope_pt (C.baseChange K) (E⁄K) h₁ h₂ hxy

noncomputable def pointFun : (E⁄K).Point → ((C • E)⁄K).Point
  | 0 => 0
  | .some x y h => .some ((C.baseChange K).ptX x) ((C.baseChange K).ptY x y) <|
      (bc_nonsingular_iff E C _ _).mp <| (nonsingular_pt_iff (C.baseChange K) (E⁄K) x y).mpr h

noncomputable def pointInv : ((C • E)⁄K).Point → (E⁄K).Point
  | 0 => 0
  | .some X Y h => .some ((C.baseChange K).invX X) ((C.baseChange K).invY X Y) <|
      (nonsingular_inv_iff (C.baseChange K) (E⁄K) X Y).mpr <| (bc_nonsingular_iff E C _ _).mpr h

variable [DecidableEq K]

noncomputable def pointEquiv : (E⁄K).Point ≃+ ((C • E)⁄K).Point where
  toFun := pointFun E C
  invFun := pointInv E C
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · simp only [pointFun, pointInv, invX_ptX, invY_ptY]
  right_inv := by
    rintro (_ | ⟨X, Y, h⟩)
    · rfl
    · simp only [pointFun, pointInv, ptX_invX, ptY_invY]
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    · rfl
    · rfl
    · rfl
    · by_cases hxy : x₁ = x₂ ∧ y₁ = (E⁄K).negY x₂ y₂
      · rcases hxy with ⟨rfl, rfl⟩
        rw [Affine.Point.add_of_Y_eq rfl rfl]
        simp only [pointFun]
        exact (Affine.Point.add_of_Y_eq rfl (bc_negY E C x₁ y₂).symm).symm
      · have hxy' : ¬((C.baseChange K).ptX x₁ = (C.baseChange K).ptX x₂ ∧ (C.baseChange K).ptY x₁ y₁ =
            ((C • E)⁄K).negY ((C.baseChange K).ptX x₂) ((C.baseChange K).ptY x₂ y₂)) := by
          rintro ⟨hx, hy⟩
          obtain rfl := (C.baseChange K).ptX_injective hx
          rw [bc_negY] at hy
          exact hxy ⟨rfl, (C.baseChange K).ptY_injective x₁ hy⟩
        rw [Affine.Point.add_some hxy]
        simp only [pointFun]
        rw [Affine.Point.add_some hxy', Affine.Point.some.injEq,
          bc_slope E C h₁.1 h₂.1 hxy, bc_addX, bc_addY]
        exact ⟨rfl, rfl⟩

@[scoped simp] lemma pointEquiv_zero : pointEquiv E C (0 : (E⁄K).Point) = 0 := rfl

@[scoped simp] lemma pointEquiv_some {x y : K} (h : (E⁄K).Nonsingular x y) :
    pointEquiv E C (.some x y h) = .some ((C.baseChange K).ptX x) ((C.baseChange K).ptY x y)
      ((bc_nonsingular_iff E C _ _).mp <| (nonsingular_pt_iff (C.baseChange K) (E⁄K) x y).mpr h) := rfl

lemma pointEquiv_smul (σ : K ≃ₐ[F] K) (P : (E⁄K).Point) :
    pointEquiv E C (σ • P) = σ • pointEquiv E C P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [algEquiv_smul_def, Affine.Point.map_some, pointEquiv_some, ptX, ptY,
      coe_baseChange_u_inv, baseChange_r, baseChange_s, baseChange_t, map_mul, map_sub, map_add,
      map_pow, AlgHom.commutes]

end VariableChange
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.WeierstrassCurve.VariableChange"

end PointEquiv
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.WeierstrassCurve.VariableChange"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.WeierstrassCurve.VariableChange P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') : ∃ e : (E⁄K).Point ≃+ (E'⁄K).Point, ∀ (σ : K ≃ₐ[F] K) (P : (E⁄K).Point), e (σ • P) = σ • e P := by
  subst hC
  exact ⟨WeierstrassCurve.VariableChange.pointEquiv E C, WeierstrassCurve.VariableChange.pointEquiv_smul E C⟩

end S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq (solution)
