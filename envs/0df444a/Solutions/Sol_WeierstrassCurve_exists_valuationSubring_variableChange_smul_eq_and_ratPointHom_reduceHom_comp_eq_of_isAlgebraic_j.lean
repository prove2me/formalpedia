-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/361371a0-35dc-5822-9556-f4142830378f

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant
import Theorems.Thm_ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic
import Theorems.Thm_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsLocalRing Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "VariableChange.map_r Affine VariableChange.mul_def VariableChange.map map_map map map_j Affine.Point.some exists_variableChange_of_j_eq VariableChange.map_t reduction VariableChange.map_s VariableChange.map_u VariableChange.map_map map_id IsIntegral toAffine Affine.Point VariableChange.map_id map_Δ Affine.Point.map Δ VariableChange Affine.map_nonsingular map_variableChange baseChange j evalEvalBC IsRationallyRepresented rationalHomSet reduceHom Affine.Y_mem_of_X_mem map_residue_Δ_ne_zero_iff reducePoint reducePoint_some_of_mem reducePoint_some_of_notMem Affine.Point.equivOfVariableChangeEq Affine.Point.some_congr ratPointMap_some ratPointMap_injective ratPointHom ratPointHom_apply pointAddEquivOfEq pointAddEquivOfEq_symm pointAddEquivOfEq_some exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant exists_map_residue_eq_and_map_subtype_j_eq exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange comp_mem_rationalHomSet Affine.Point.vcInvFun_add"
namespace AlgebraisationAL
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

section VC

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K)
  (W : WeierstrassCurve.Affine K)

theorem vcFun_injective : Function.Injective (vcFun C W) :=
  (vcFun_leftInverse (C := C) (W := W)).injective

theorem vcFun_add' (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  have hP := vcFun_leftInverse (C := C) (W := W) P
  have hQ := vcFun_leftInverse (C := C) (W := W) Q
  conv_lhs => rw [← hP, ← hQ, ← WeierstrassCurve.Affine.Point.vcInvFun_add C W]
  exact vcFun_rightInverse (C := C) (W := W) _

theorem vcInvFun_add' (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q :=
  WeierstrassCurve.Affine.Point.vcInvFun_add C W P Q

def vcHom : (C • W).toAffine.Point →+ W.Point where
  toFun := vcFun C W
  map_zero' := rfl
  map_add' P Q := vcFun_add' C W P Q

def vcInvHom : W.Point →+ (C • W).toAffine.Point where
  toFun := vcInvFun C W
  map_zero' := rfl
  map_add' := vcInvFun_add' C W

@[scoped simp] theorem vcHom_apply (P : (C • W).toAffine.Point) : vcHom C W P = vcFun C W P := rfl
@[scoped simp] theorem vcInvHom_apply (P : W.Point) : vcInvHom C W P = vcInvFun C W P := rfl

omit [DecidableEq K] in
theorem vcInvFun_some' {x y : K} (h : W.Nonsingular x y) :
    vcInvFun C W (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

omit [DecidableEq K] in
theorem vcFun_some' {x y : K} (h : (C • W).toAffine.Nonsingular x y) :
    vcFun C W (.some x y h) = .some (vcX C x) (vcY C x y)
      ((nonsingular_variableChange_iff x y).mp h) := rfl

theorem equivOfVariableChangeEq_symm_some {V : WeierstrassCurve.Affine K} (h : C • W = V)
    {x y : K} (hxy : W.Nonsingular x y) :
    ∃ h', (equivOfVariableChangeEq h).symm (.some x y hxy) =
      .some (vcXInv C x) (vcYInv C x y) h' := by
  subst h
  exact ⟨_, rfl⟩

theorem equivOfVariableChangeEq_symm_zero {V : WeierstrassCurve.Affine K} (h : C • W = V) :
    (equivOfVariableChangeEq h).symm 0 = 0 := by
  subst h
  rfl

theorem vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem map_vcXInv {K' : Type*} [Field K'] (f : K ≃+* K') (C : VariableChange K) (x : K) :
    f (vcXInv C x) = vcXInv (C.map f.toRingHom) (f x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

theorem map_vcYInv {K' : Type*} [Field K'] (f : K ≃+* K') (C : VariableChange K) (x y : K) :
    f (vcYInv C x y) = vcYInv (C.map f.toRingHom) (f x) (f y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

end VC

section Rational

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
theorem evalEvalBC_self (p : K[X][Y]) (x y : K) :
    WeierstrassCurve.evalEvalBC K p x y = p.evalEval x y := by
  simp [WeierstrassCurve.evalEvalBC, Polynomial.map_id]

variable (C : VariableChange K) (X : WeierstrassCurve K)

theorem isRationallyRepresented_vcInvHom :
    IsRationallyRepresented K X (C • X) (vcInvHom C X) := by
  set c : K := ((C.u⁻¹ : Kˣ) : K) with hc
  refine ⟨Polynomial.C (Polynomial.C (c ^ 2) * (Polynomial.X - Polynomial.C C.r)), 1,
    Polynomial.C (Polynomial.C (c ^ 3)) *
      (Polynomial.X - Polynomial.C (Polynomial.C C.t +
        Polynomial.C C.s * (Polynomial.X - Polynomial.C C.r))), 1,
    ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = 1 := by
    rw [evalEvalBC_self, evalEval_one]
  have e1 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (c ^ 2) * (Polynomial.X - Polynomial.C C.r))) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcXInv C x := by
    rw [e0, div_one, evalEvalBC_self, evalEval_C]
    simp [vcXInv, hc]
  have e2 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (c ^ 3)) *
        (Polynomial.X - Polynomial.C (Polynomial.C C.t +
          Polynomial.C C.s * (Polynomial.X - Polynomial.C C.r)))) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcYInv C x y := by
    rw [e0, div_one, evalEvalBC_self]
    simp only [evalEval_mul, evalEval_C, evalEval_sub, evalEval_X, eval_C,
      eval_add, eval_mul, eval_sub, eval_X]
    simp [vcYInv, hc]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : K, a = vcXInv C x → b = vcYInv C x y →
      ∃ h', vcInvHom C X (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, rfl⟩

theorem isRationallyRepresented_vcHom :
    IsRationallyRepresented K (C • X) X (vcHom C X) := by
  set u : K := ((C.u : Kˣ) : K) with hu
  refine ⟨Polynomial.C (Polynomial.C (u ^ 2) * Polynomial.X + Polynomial.C C.r), 1,
    Polynomial.C (Polynomial.C (u ^ 3)) * Polynomial.X +
      Polynomial.C (Polynomial.C (u ^ 2 * C.s) * Polynomial.X + Polynomial.C C.t), 1,
    ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = 1 := by
    rw [evalEvalBC_self, evalEval_one]
  have e1 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (u ^ 2) * Polynomial.X + Polynomial.C C.r)) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcX C x := by
    rw [e0, div_one, evalEvalBC_self, evalEval_C]
    simp [vcX, hu]
  have e2 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (u ^ 3)) * Polynomial.X +
        Polynomial.C (Polynomial.C (u ^ 2 * C.s) * Polynomial.X + Polynomial.C C.t)) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcY C x y := by
    rw [e0, div_one, evalEvalBC_self]
    simp only [evalEval_mul, evalEval_C, evalEval_X, eval_C, evalEval_add,
      eval_add, eval_mul, eval_X]
    simp [vcY, hu]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : K, a = vcX C x → b = vcY C x y →
      ∃ h', vcHom C X (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, rfl⟩

def theta {X X₂ : WeierstrassCurve K} (C : VariableChange K) (h : C • X = X₂) :
    X.toAffine.Point →+ X₂.toAffine.Point :=
  (WeierstrassCurve.pointAddEquivOfEq h).toAddMonoidHom.comp (vcInvHom C X)

def theta' {X X₂ : WeierstrassCurve K} (C : VariableChange K) (h : C • X = X₂) :
    X₂.toAffine.Point →+ X.toAffine.Point :=
  (vcHom C X).comp (WeierstrassCurve.pointAddEquivOfEq h).symm.toAddMonoidHom

variable {C X}

theorem theta_mem {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    theta C h ∈ rationalHomSet K X X₂ := by
  subst h
  refine Or.inr ?_
  have : theta C (rfl : C • X = C • X) = vcInvHom C X := by
    ext P; simp [theta]
  rw [this]
  exact isRationallyRepresented_vcInvHom C X

theorem theta'_mem {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    theta' C h ∈ rationalHomSet K X₂ X := by
  subst h
  refine Or.inr ?_
  have : theta' C (rfl : C • X = C • X) = vcHom C X := by
    ext P; simp [theta']
  rw [this]
  exact isRationallyRepresented_vcHom C X

theorem theta_theta' {X₂ : WeierstrassCurve K} (h : C • X = X₂) (Q : X₂.toAffine.Point) :
    theta C h (theta' C h Q) = Q := by
  subst h
  simp [theta, theta']
  exact vcFun_leftInverse (C := C) (W := X) Q

theorem theta'_theta {X₂ : WeierstrassCurve K} (h : C • X = X₂) (P : X.toAffine.Point) :
    theta' C h (theta C h P) = P := by
  subst h
  simp [theta, theta']
  exact vcFun_rightInverse (C := C) (W := X) P

theorem theta_some {X₂ : WeierstrassCurve K} (h : C • X = X₂) {x y : K}
    (hxy : X.toAffine.Nonsingular x y) :
    ∃ h', theta C h (.some x y hxy) = .some (vcXInv C x) (vcYInv C x y) h' := by
  subst h
  exact ⟨(nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
    (by rwa [vcX_vcXInv, vcY_vcYInv]), by simp [theta, vcInvFun_some']⟩

end Rational

section Reduce

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)]

@[scoped simp] theorem reduceHom_apply {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : reduceHom hΔ P = reducePoint hΔ P := rfl

omit [DecidableEq L] in
private theorem _root_.WeierstrassCurve.AlgebraisationAL.some_congr {V : WeierstrassCurve.Affine (ResidueField A)} {x₁ x₂ y₁ y₂ : ResidueField A}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

p2m_export "WeierstrassCurve.AlgebraisationAL" "some_congr"

theorem reduce_theta (E' : WeierstrassCurve A) (w : VariableChange A)
    (hΔ' : (E'.map (residue A)).Δ ≠ 0) (hΔ : ((w • E').map (residue A)).Δ ≠ 0)
    (hred : (w • E').map (residue A) = w.map (residue A) • E'.map (residue A))
    (hL : (w.map A.subtype) • (E'.map A.subtype) = (w • E').map A.subtype)
    (P : (E'.map A.subtype).toAffine.Point) :
    WeierstrassCurve.pointAddEquivOfEq hred (reduceHom hΔ (theta (w.map A.subtype) hL P)) =
      vcInvFun (w.map (residue A)) _ (reduceHom hΔ' P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · have h0 : theta (w.map A.subtype) hL (0 : (E'.map A.subtype).toAffine.Point) = 0 :=
      map_zero _
    change WeierstrassCurve.pointAddEquivOfEq hred (reduceHom hΔ (theta (w.map A.subtype) hL 0))
      = vcInvFun _ _ (reduceHom hΔ' 0)
    rw [h0, _root_.map_zero, _root_.map_zero, _root_.map_zero]
    rfl
  · obtain ⟨h₁, hθ⟩ := theta_some hL hP
    erw [hθ]
    have hu : (((w.map A.subtype).u⁻¹ : Lˣ) : L) = (((w.u⁻¹ : Aˣ) : A) : L) := by
      rw [VariableChange.map_u, Units.coe_map_inv]; rfl
    have hr : (w.map A.subtype).r = (w.r : L) := VariableChange.map_r _ _
    have hs : (w.map A.subtype).s = (w.s : L) := VariableChange.map_s _ _
    have ht : (w.map A.subtype).t = (w.t : L) := VariableChange.map_t _ _
    have huk : (((w.map (residue A)).u⁻¹ : (ResidueField A)ˣ) : ResidueField A)
        = residue A ((w.u⁻¹ : Aˣ) : A) := by
      rw [VariableChange.map_u, Units.coe_map_inv]; rfl
    have hrk : (w.map (residue A)).r = residue A w.r := VariableChange.map_r _ _
    have hsk : (w.map (residue A)).s = residue A w.s := VariableChange.map_s _ _
    have htk : (w.map (residue A)).t = residue A w.t := VariableChange.map_t _ _
    by_cases hx : x ∈ A
    ·
      have hy : y ∈ A := Affine.Y_mem_of_X_mem E' hP.1 hx
      set X₁A : A := ((w.u⁻¹ : Aˣ) : A) ^ 2 * (⟨x, hx⟩ - w.r) with hX₁A
      set Y₁A : A := ((w.u⁻¹ : Aˣ) : A) ^ 3 * (⟨y, hy⟩ - w.t - w.s * (⟨x, hx⟩ - w.r)) with hY₁A
      have hX₁ : vcXInv (w.map A.subtype) x = (X₁A : L) := by
        simp only [vcXInv, hu, hr, hX₁A]
        push_cast
        ring
      have hY₁ : vcYInv (w.map A.subtype) x y = (Y₁A : L) := by
        simp only [vcYInv, hu, hr, hs, ht, hY₁A]
        push_cast
        ring
      have hX₁mem : vcXInv (w.map A.subtype) x ∈ A := by rw [hX₁]; exact X₁A.2
      rw [reduceHom_apply, reducePoint_some_of_mem hΔ h₁ hX₁mem,
        WeierstrassCurve.pointAddEquivOfEq_some, reduceHom_apply,
        reducePoint_some_of_mem hΔ' hP hx, vcInvFun_some']
      refine some_congr ?_ ?_ _ _
      · rw [ValuationSubring.residue_eq_of_coe_eq (A := A) hX₁mem (v := X₁A) hX₁]
        simp only [vcXInv, huk, hrk, hX₁A, map_mul, map_pow, map_sub]
      · rw [ValuationSubring.residue_eq_of_coe_eq (A := A) _ (v := Y₁A) hY₁]
        simp only [vcYInv, huk, hrk, hsk, htk, hY₁A, map_mul, map_pow, map_sub]
    ·
      have hX₁ : vcXInv (w.map A.subtype) x ∉ A := by
        intro hmem
        apply hx
        have hx' : x = vcX (w.map A.subtype) (vcXInv (w.map A.subtype) x) :=
          (vcX_vcXInv x).symm
        rw [hx', vcX]
        refine A.toSubring.add_mem (A.toSubring.mul_mem (pow_mem ?_ 2) hmem) ?_
        · rw [VariableChange.map_u, Units.coe_map]; exact SetLike.coe_mem _
        · rw [hr]; exact SetLike.coe_mem _
      rw [reduceHom_apply, reducePoint_some_of_notMem hΔ h₁ hX₁, _root_.map_zero, reduceHom_apply,
        reducePoint_some_of_notMem hΔ' hP hx]
      rfl

end Reduce

section Places

abbrev Qbar : Type := AlgebraicClosure ℚ

theorem algebraRat_eq :
    (AlgebraicClosure.instAlgebra ℚ : Algebra ℚ Qbar) = (inferInstance : Algebra ℚ Qbar) :=
  Subsingleton.elim _ _

theorem isAlgebraic_rat : Algebra.IsAlgebraic ℚ Qbar := by
  have h := AlgebraicClosure.isAlgebraic (k := ℚ)
  rwa [algebraRat_eq] at h

theorem isAlgebraic_int : @Algebra.IsAlgebraic ℤ Qbar _ _ (Ring.toIntAlgebra Qbar) := by
  haveI := isAlgebraic_rat
  have h : Algebra.IsAlgebraic ℤ Qbar :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := Qbar)).mpr inferInstance
  convert h
  rfl

theorem mem_range_of_eval₂_eq_zero {k K' : Type*} [Field k] [Field K'] [IsAlgClosed k]
    (f : k →+* K') {q : k[X]} (hq : q ≠ 0) {z : K'} (hz : q.eval₂ f z = 0) :
    z ∈ Set.range f := by
  letI : Algebra k K' := f.toAlgebra
  have hint : _root_.IsIntegral k z := isAlgebraic_iff_isIntegral.mp ⟨q, hq, hz⟩
  haveI : FiniteDimensional k (IntermediateField.adjoin k {z}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hbot : IntermediateField.adjoin k {z} = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hz' : z ∈ (⊥ : IntermediateField k K') :=
    hbot ▸ IntermediateField.mem_adjoin_simple_self k z
  rwa [IntermediateField.mem_bot] at hz'

variable {L : Type*} [Field L] (ι : Qbar →+* L) (B : ValuationSubring L)

def placeOf : ValuationSubring Qbar := B.comap ι

theorem mem_placeOf {x : Qbar} : x ∈ placeOf ι B ↔ ι x ∈ B := Iff.rfl

def toB : placeOf ι B →+* B :=
  ι.restrict (placeOf ι B) B (fun _ hx => hx)

@[scoped simp] theorem coe_toB (a : placeOf ι B) : (toB ι B a : L) = ι a := rfl

scoped instance isLocalHom_toB : IsLocalHom (toB ι B) := by
  constructor
  intro a ha
  have ha0 : (a : Qbar) ≠ 0 := by
    intro h
    apply ha.ne_zero
    ext
    simp [h]
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hbL : ι a * (b : L) = 1 := by
    have := congrArg (fun z : B => (z : L)) hb
    simpa using this
  have hb' : (b : L) = ι ((a : Qbar)⁻¹) := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_right hbL
  have hinv : (a : Qbar)⁻¹ ∈ placeOf ι B := by
    show ι _ ∈ B
    rw [← hb']
    exact b.2
  exact ⟨⟨a, ⟨(a : Qbar)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0),
    Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

def resMap : ResidueField (placeOf ι B) →+* ResidueField B :=
  ResidueField.map (toB ι B)

theorem resMap_residue (a : placeOf ι B) :
    resMap ι B (residue _ a) = residue B (toB ι B a) := rfl

theorem injective_resMap : Function.Injective (resMap ι B) := (resMap ι B).injective

theorem surjective_resMap (p : ℕ) [Fact p.Prime]
    (hpow : ∀ z : ResidueField B, ∃ n : ℕ, 0 < n ∧ z ^ p ^ n = z) :
    Function.Surjective (resMap ι B) := by
  intro z
  obtain ⟨n, hn, hz⟩ := hpow z
  haveI : IsAlgClosed (ResidueField (placeOf ι B)) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat _
  have hp : 1 < p ^ n := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  have hq : (Polynomial.X ^ (p ^ n) - Polynomial.X : (ResidueField (placeOf ι B))[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ hp
  obtain ⟨y, hy⟩ := mem_range_of_eval₂_eq_zero (resMap ι B) hq (z := z)
    (by simp [eval₂_sub, eval₂_X_pow, eval₂_X, hz])
  exact ⟨y, hy⟩

def resEquiv (h : Function.Surjective (resMap ι B)) :
    ResidueField (placeOf ι B) ≃+* ResidueField B :=
  RingEquiv.ofBijective (resMap ι B) ⟨injective_resMap ι B, h⟩

@[scoped simp] theorem resEquiv_apply (h : Function.Surjective (resMap ι B)) (x : ResidueField (placeOf ι B)) :
    resEquiv ι B h x = resMap ι B x := rfl

theorem resEquiv_toRingHom (h : Function.Surjective (resMap ι B)) :
    (resEquiv ι B h).toRingHom = resMap ι B := rfl

end Places

section Iota

variable {L : Type} [Field L] [DecidableEq L] (ι : Qbar →+* L) (B : ValuationSubring L)
  [DecidableEq Qbar] [DecidableEq (ResidueField B)] [DecidableEq (ResidueField (placeOf ι B))]

theorem reduce_iota_some (E : WeierstrassCurve (placeOf ι B))
    (hΔ : (E.map (residue (placeOf ι B))).Δ ≠ 0)
    (hΔι : ((E.map (toB ι B)).map (residue B)).Δ ≠ 0) {x y : Qbar}
    (h : (E.map (placeOf ι B).subtype).toAffine.Nonsingular x y)
    (h' : ((E.map (toB ι B)).map B.subtype).toAffine.Nonsingular (ι x) (ι y)) :
    reduceHom hΔι (.some (ι x) (ι y) h') = ratPointHom (resMap ι B) (reduceHom hΔ (.some x y h)) := by
  rw [reduceHom_apply, reduceHom_apply]
  by_cases hx : x ∈ placeOf ι B
  · have hιx : ι x ∈ B := hx
    have hy : y ∈ placeOf ι B := Affine.Y_mem_of_X_mem E h.1 hx
    have hιy : ι y ∈ B := hy
    rw [reducePoint_some_of_mem hΔι h' hιx, reducePoint_some_of_mem hΔ h hx, ratPointHom_apply,
      ratPointMap_some]
    rfl
  · have hιx : ι x ∉ B := hx
    rw [reducePoint_some_of_notMem hΔι h' hιx, reducePoint_some_of_notMem hΔ h hx]
    rfl

end Iota

section Main

variable {L : Type} [Field L] [IsAlgClosed L] [CharZero L] [DecidableEq L]
  (B : ValuationSubring L) [DecidableEq (ResidueField B)] [DecidableEq Qbar]

open scoped Classical in
theorem main (p : ℕ) [Fact p.Prime] (A₀ : ValuationSubring Qbar)
    [DecidableEq (ResidueField A₀)] [CharP (ResidueField A₀) p]
    (W : WeierstrassCurve (ResidueField A₀)) (β₀ : W.toAffine.Point → W.toAffine.Point)
    (φ : ResidueField A₀ ≃+* ResidueField B)
    (E' : WeierstrassCurve B) [E'.IsElliptic] (hΔ' : (E'.map (residue B)).Δ ≠ 0)
    (hj : IsAlgebraic ℚ (E'.map B.subtype).j)
    (v' : VariableChange (ResidueField B)) (hv' : v' • E'.map (residue B) = W.map φ.toRingHom)
    {β' : (E'.map B.subtype).toAffine.Point →+ (E'.map B.subtype).toAffine.Point}
    (hβ' : β' ∈ rationalHomSet L (E'.map B.subtype) (E'.map B.subtype))
    (hcompat : ∀ (Q : (E'.map B.subtype).toAffine.Point) (P₀ : W.toAffine.Point),
      ratPointHom φ.toRingHom P₀ = (equivOfVariableChangeEq hv').symm (reduceHom hΔ' Q) →
      ratPointHom φ.toRingHom (β₀ P₀) =
        (equivOfVariableChangeEq hv').symm (reduceHom hΔ' (β' Q))) :
    ∃ (A' : ValuationSubring Qbar) (e : ResidueField A' ≃+* ResidueField A₀)
      (E : WeierstrassCurve A') (hΔ : (E.map (residue A')).Δ ≠ 0)
      (v : VariableChange (ResidueField A₀)) (hv : v • (E.map (residue A')).map e.toRingHom = W),
      ∃ α ∈ rationalHomSet Qbar (E.map A'.subtype) (E.map A'.subtype),
        ∀ P : (E.map A'.subtype).toAffine.Point,
          (equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ (α P))) =
            β₀ ((equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ P))) := by
  classical

  haveI hQalg := isAlgebraic_rat
  obtain ⟨ι⟩ : Nonempty (Qbar →+* L) := ⟨(IsAlgClosed.lift : Qbar →ₐ[ℚ] L).toRingHom⟩

  haveI hcharB : CharP (ResidueField B) p := charP_of_injective_ringHom φ.toRingHom.injective p
  haveI := isAlgebraic_int
  have hpow : ∀ z : ResidueField B, ∃ n : ℕ, 0 < n ∧ z ^ p ^ n = z := by
    intro z
    obtain ⟨n, hn, h⟩ :=
      ValuationSubring.exists_pow_prime_pow_eq_self_of_isAlgebraic A₀ p (φ.symm z)
    refine ⟨n, hn, φ.symm.injective ?_⟩
    rw [map_pow, h]
  have hsurj := surjective_resMap ι B p hpow
  set A' : ValuationSubring Qbar := placeOf ι B with hA'
  set ê : ResidueField A' ≃+* ResidueField B := resEquiv ι B hsurj with hê
  set eDL : ResidueField A' ≃+* ResidueField A₀ := ê.trans φ.symm with heDL

  have hjB : (E'.map B.subtype).j = ((E'.j : B) : L) := by rw [map_j]; rfl
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Qbar, ι j₀ = (E'.map B.subtype).j := by
    obtain ⟨f, hf0, hf⟩ := hj
    have hq : f.map (algebraMap ℚ Qbar) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ Qbar).injective).mpr hf0
    have hz : (f.map (algebraMap ℚ Qbar)).eval₂ ι (E'.map B.subtype).j = 0 := by
      rw [eval₂_map, Subsingleton.elim (ι.comp (algebraMap ℚ Qbar)) (algebraMap ℚ L)]
      exact hf
    exact mem_range_of_eval₂_eq_zero ι hq hz
  have hj₀A : j₀ ∈ A' := by
    show ι j₀ ∈ B
    rw [hj₀, hjB]
    exact (E'.j).2

  haveI hE'ell : (E'.map (residue B)).IsElliptic := ⟨hΔ'.isUnit⟩
  have hres : residue A' ⟨j₀, hj₀A⟩ = ((E'.map (residue B)).map ê.symm.toRingHom).j := by
    rw [map_j, map_j]
    apply ê.injective
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    show resMap ι B (residue _ ⟨j₀, hj₀A⟩) = residue B E'.j
    rw [resMap_residue]
    congr 1
    apply Subtype.ext
    rw [coe_toB]
    exact hj₀.trans hjB
  obtain ⟨E, hEell, hEred, hEj⟩ :=
    WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq A' _ ⟨j₀, hj₀A⟩ hres
  have hEΔ : (E.map (residue A')).Δ ≠ 0 := by
    rw [hEred, map_Δ]
    exact (_root_.map_ne_zero _).mpr hE'ell.isUnit.ne_zero
  have hEunit : IsUnit E.Δ := (map_residue_Δ_ne_zero_iff E).mp hEΔ
  have hE'unit : IsUnit E'.Δ := (map_residue_Δ_ne_zero_iff E').mp hΔ'

  set Eι : WeierstrassCurve B := E.map (toB ι B) with hEι
  have hEιunit : IsUnit Eι.Δ := by rw [hEι, map_Δ]; exact hEunit.map _
  haveI : Eι.IsElliptic := ⟨hEιunit⟩
  have hjL : (Eι.map B.subtype).j = (E'.map B.subtype).j := by
    have h1 : (Eι.map B.subtype).j = ((E.map A'.subtype).map ι).j := rfl
    rw [h1, map_j, hEj, hj₀]
  obtain ⟨ψ, hψ⟩ :=
    WeierstrassCurve.exists_variableChange_of_j_eq (Eι.map B.subtype) (E'.map B.subtype) hjL
  obtain ⟨ψB, hψB, hψE⟩ :=
    WeierstrassCurve.exists_variableChange_map_subtype_eq_and_smul_eq_of_isUnit_discriminant B Eι E'
      hEιunit hE'unit ψ hψ
  subst hψE

  set ψk : VariableChange (ResidueField B) := ψB.map (residue B) with hψk
  have hred : (ψB • Eι).map (residue B) = ψk • Eι.map (residue B) :=
    (map_variableChange Eι ψB (residue B)).symm
  have hEιΔ : (Eι.map (residue B)).Δ ≠ 0 := (map_residue_Δ_ne_zero_iff Eι).mpr hEιunit
  letI : Algebra Qbar L := ι.toAlgebra
  set X : WeierstrassCurve Qbar := E.map A'.subtype with hX
  haveI : X.IsElliptic := hEell
  have hL : (ψB.map B.subtype) • (X.baseChange L) = (ψB • Eι).map B.subtype :=
    map_variableChange Eι ψB B.subtype
  set θ := theta (ψB.map B.subtype) hL with hθdef
  set θ' := theta' (ψB.map B.subtype) hL with hθ'def
  have hθ : θ ∈ rationalHomSet L (X.baseChange L) ((ψB • Eι).map B.subtype) := theta_mem hL
  have hθ' : θ' ∈ rationalHomSet L ((ψB • Eι).map B.subtype) (X.baseChange L) := theta'_mem hL
  set β'' := θ'.comp (β'.comp θ) with hβ''def
  have hβ'' : β'' ∈ rationalHomSet L (X.baseChange L) (X.baseChange L) :=
    comp_mem_rationalHomSet L _ _ _ (comp_mem_rationalHomSet L _ _ _ hθ hβ') hθ'
  obtain ⟨α, hαmem, hα⟩ :=
    exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
      (k := Qbar) L X X hβ''

  set vB : VariableChange (ResidueField B) := v' * ψk with hvB
  have hvBeq : vB • Eι.map (residue B) = W.map φ.toRingHom := by
    rw [hvB, mul_smul, ← hred]
    exact hv'
  set v : VariableChange (ResidueField A₀) := vB.map φ.symm.toRingHom with hv_def
  have hcurve : (E.map (residue A')).map eDL.toRingHom =
      (Eι.map (residue B)).map φ.symm.toRingHom := rfl
  have hv : v • (E.map (residue A')).map eDL.toRingHom = W := by
    rw [hcurve, hv_def, map_variableChange, hvBeq, map_map,
      RingEquiv.symm_toRingHom_comp_toRingHom, WeierstrassCurve.map_id]

  set ePt : (E.map (residue A')).toAffine.Point →+ (Eι.map (residue B)).toAffine.Point :=
    ratPointHom (resMap ι B) with hePt
  have ePt_some : ∀ {a b : ResidueField A'} (hab : (E.map (residue A')).toAffine.Nonsingular a b),
      ∃ h', ePt (.some a b hab) = .some (resMap ι B a) (resMap ι B b) h' :=
    fun hab => ⟨_, rfl⟩
  have hιpt : ∀ R : X.toAffine.Point,
      reduceHom hEιΔ (Affine.Point.map (W' := X) (IsScalarTower.toAlgHom Qbar Qbar L) R) =
        ePt (reduceHom hEΔ R) := by
    intro R
    rcases R with _ | ⟨x, y, h⟩
    · rfl
    · exact reduce_iota_some ι B E hEΔ hEιΔ h _
  have hφe : ∀ c : ResidueField A', φ (eDL.toRingHom c) = resMap ι B c := fun c => by
    rw [heDL, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, hê, resEquiv_apply]
  have hvmap : v.map φ.toRingHom = vB := by
    rw [hv_def, VariableChange.map_map, RingEquiv.toRingHom_comp_symm_toRingHom,
      VariableChange.map_id]
  have hkey : ∀ R : X.toAffine.Point,
      ratPointHom φ.toRingHom ((equivOfVariableChangeEq hv).symm
        (ratPointHom eDL.toRingHom (reduceHom hEΔ R))) =
      (equivOfVariableChangeEq hv').symm ((WeierstrassCurve.pointAddEquivOfEq hred).symm
        (vcInvFun ψk _ (ePt (reduceHom hEΔ R)))) := by
    intro R
    rcases reduceHom hEΔ R with _ | ⟨a, b, hab⟩
    · have l1 : (equivOfVariableChangeEq hv).symm
          (ratPointHom eDL.toRingHom (0 : (E.map (residue A')).toAffine.Point)) = 0 :=
        equivOfVariableChangeEq_symm_zero v _ hv
      have r1 : vcInvFun ψk (Eι.map (residue B)) (ePt 0) = 0 := rfl
      change ratPointHom φ.toRingHom ((equivOfVariableChangeEq hv).symm
          (ratPointHom eDL.toRingHom (0 : (E.map (residue A')).toAffine.Point))) =
        (equivOfVariableChangeEq hv').symm ((WeierstrassCurve.pointAddEquivOfEq hred).symm
          (vcInvFun ψk _ (ePt 0)))
      rw [l1, r1, _root_.map_zero, _root_.map_zero, equivOfVariableChangeEq_symm_zero]
    · obtain ⟨h0, e0⟩ := ePt_some hab
      rw [e0, ratPointHom_apply, ratPointHom_apply, ratPointMap_some (f := eDL.toRingHom)]
      obtain ⟨h1, e1⟩ := equivOfVariableChangeEq_symm_some v _ hv
        ((WeierstrassCurve.Affine.map_nonsingular _ eDL.toRingHom.injective a b).mpr hab)
      rw [e1, ratPointMap_some (f := φ.toRingHom), vcInvFun_some',
        WeierstrassCurve.pointAddEquivOfEq_symm, WeierstrassCurve.pointAddEquivOfEq_some]
      obtain ⟨h2, e2⟩ := equivOfVariableChangeEq_symm_some v' _ hv'
        (x := vcXInv ψk (resMap ι B a)) (y := vcYInv ψk (resMap ι B a) (resMap ι B b))
        (hred ▸ (nonsingular_variableChange_iff _ _).mpr (by
          rw [vcX_vcXInv, vcY_vcYInv]
          exact h0))
      rw [e2]
      refine Affine.Point.some_congr ?_ ?_ _ _
      · show φ (vcXInv v (eDL.toRingHom a)) = _
        rw [map_vcXInv φ, hφe, hvmap, hvB, vcXInv_mul]
      · show φ (vcYInv v (eDL.toRingHom a) (eDL.toRingHom b)) = _
        rw [map_vcYInv φ, hφe, hφe, hvmap, hvB, vcYInv_mul]

  refine ⟨A', eDL, E, hEΔ, v, hv, α, hαmem, fun P => ?_⟩
  have hredθ : ∀ R : X.toAffine.Point,
      reduceHom hΔ' (θ (Affine.Point.map (W' := X) (IsScalarTower.toAlgHom Qbar Qbar L) R)) =
        (WeierstrassCurve.pointAddEquivOfEq hred).symm
          (vcInvFun ψk _ (ePt (reduceHom hEΔ R))) := by
    intro R
    have h1 := reduce_theta Eι ψB hEιΔ hΔ' hred hL
      (Affine.Point.map (W' := X) (IsScalarTower.toAlgHom Qbar Qbar L) R)
    rw [hιpt R] at h1
    rw [← h1, AddEquiv.symm_apply_apply]
    rfl
  set P₀ := (equivOfVariableChangeEq hv).symm (ratPointHom eDL.toRingHom (reduceHom hEΔ P))
    with hP₀
  set Q := θ (Affine.Point.map (W' := X) (IsScalarTower.toAlgHom Qbar Qbar L) P) with hQ
  have hprem : ratPointHom φ.toRingHom P₀ = (equivOfVariableChangeEq hv').symm (reduceHom hΔ' Q) := by
    rw [hQ, hredθ, hP₀]
    exact hkey P
  have hc := hcompat Q P₀ hprem
  have hβQ : β' Q = θ (Affine.Point.map (W' := X) (IsScalarTower.toAlgHom Qbar Qbar L) (α P)) := by
    rw [← hα P]
    show β' Q = θ (θ' (β' (θ _)))
    rw [theta_theta']
  rw [hβQ, hredθ, ← hkey (α P), ratPointHom_apply, ratPointHom_apply] at hc
  exact (ratPointMap_injective φ.toRingHom hc).symm

end Main

end WeierstrassCurve.AlgebraisationAL
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve.AlgebraisationAL"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j.WeierstrassCurve.AlgebraisationAL"

open scoped Classical in
theorem solution (p : ℕ) [Fact p.Prime] (A₀ : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A₀)] [CharP (IsLocalRing.ResidueField A₀) p] (W : WeierstrassCurve (IsLocalRing.ResidueField A₀)) (β₀ : W.toAffine.Point → W.toAffine.Point) {L : Type} [Field L] [IsAlgClosed L] [CharZero L] [DecidableEq L] (B : ValuationSubring L) [DecidableEq (IsLocalRing.ResidueField B)] (φ : IsLocalRing.ResidueField A₀ ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B) [E'.IsElliptic] (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0) (hj : IsAlgebraic ℚ (E'.map B.subtype).j) (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B)) (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom) {β' : (E'.map B.subtype).toAffine.Point →+ (E'.map B.subtype).toAffine.Point} (hβ' : β' ∈ WeierstrassCurve.rationalHomSet L (E'.map B.subtype) (E'.map B.subtype)) (hcompat : ∀ (Q : (E'.map B.subtype).toAffine.Point) (P₀ : W.toAffine.Point), WeierstrassCurve.ratPointHom φ.toRingHom P₀ = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' Q) → WeierstrassCurve.ratPointHom φ.toRingHom (β₀ P₀) = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' (β' Q))) : ∃ (A' : ValuationSubring (AlgebraicClosure ℚ)) (e : IsLocalRing.ResidueField A' ≃+* IsLocalRing.ResidueField A₀) (E : WeierstrassCurve A') (hΔ : (E.map (IsLocalRing.residue A')).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A₀)) (hv : v • (E.map (IsLocalRing.residue A')).map e.toRingHom = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A'.subtype) (E.map A'.subtype), ∀ P : (E.map A'.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.ratPointHom e.toRingHom (WeierstrassCurve.reduceHom hΔ (α P))) = β₀ ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.ratPointHom e.toRingHom (WeierstrassCurve.reduceHom hΔ P))) :=
  WeierstrassCurve.AlgebraisationAL.main B p A₀ W β₀ φ E' hΔ' hj v' hv' hβ' hcompat

end S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j (solution)
