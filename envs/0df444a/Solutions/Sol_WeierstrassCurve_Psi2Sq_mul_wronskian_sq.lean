-- Prove2me | solution 1 for WeierstrassCurve.Psi2Sq_mul_wronskian_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c8b691d1-1223-5444-ac83-f342d40dcf86

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
p2m_open "WeierstrassCurve"

namespace InvariantDerivation

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

abbrev A : Type _ := W.toAffine.CoordinateRing

abbrev L : Type _ := FractionRing (A W)

abbrev T : Type _ := TrivSqZeroExt (L W) (L W)

scoped instance instIsDomainA : IsDomain (A W) := inferInstance
noncomputable scoped instance instFieldL : Field (L W) := inferInstance
noncomputable scoped instance instCommRingL : CommRing (L W) := inferInstance
noncomputable scoped instance instAlgKA : Algebra K (A W) := inferInstance
noncomputable scoped instance instAlgKL : Algebra K (L W) := inferInstance
noncomputable scoped instance instAlgAL : Algebra (A W) (L W) := inferInstance
noncomputable scoped instance instModL : Module (L W) (L W) := inferInstance
noncomputable scoped instance instModLop : Module (L W)ᵐᵒᵖ (L W) := inferInstance
scoped instance instCentral : IsCentralScalar (L W) (L W) := inferInstance
noncomputable scoped instance instCommRingT : CommRing (T W) := inferInstance
noncomputable scoped instance instRingT : Ring (T W) := inferInstance
noncomputable scoped instance instSemiringT : Semiring (T W) := inferInstance
noncomputable scoped instance instMonoidT : Monoid (T W) := inferInstance
noncomputable scoped instance instMulT : Mul (T W) := inferInstance
noncomputable scoped instance instAddT : Add (T W) := inferInstance
noncomputable scoped instance instAddCommMonoidT : AddCommMonoid (T W) := inferInstance

noncomputable def x₀ : L W := algebraMap (A W) (L W) (AdjoinRoot.mk _ (C X))

noncomputable def y₀ : L W := algebraMap (A W) (L W) (AdjoinRoot.mk _ Y)

noncomputable def fY : L W :=
  2 * y₀ W + algebraMap K (L W) W.a₁ * x₀ W + algebraMap K (L W) W.a₃

noncomputable def negfX : L W :=
  3 * x₀ W ^ 2 + 2 * algebraMap K (L W) W.a₂ * x₀ W + algebraMap K (L W) W.a₄
    - algebraMap K (L W) W.a₁ * y₀ W

noncomputable def i₀ : K →+* T W := (TrivSqZeroExt.inlHom (L W) (L W)).comp (algebraMap K (L W))

noncomputable def tX : T W := TrivSqZeroExt.inl (x₀ W) + TrivSqZeroExt.inr (fY W)

noncomputable def tY : T W := TrivSqZeroExt.inl (y₀ W) + TrivSqZeroExt.inr (negfX W)

noncomputable def Φ₀ : K[X][Y] →+* T W :=
  eval₂RingHom (eval₂RingHom (i₀ W) (tX W)) (tY W)

noncomputable def fstRingHom : T W →+* L W where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

@[scoped simp] theorem fstRingHom_apply (z : T W) : fstRingHom W z = z.fst := rfl

@[scoped simp] theorem fst_tX : (tX W).fst = x₀ W := by simp [tX]
@[scoped simp] theorem snd_tX : (tX W).snd = fY W := by simp [tX]
@[scoped simp] theorem fst_tY : (tY W).fst = y₀ W := by simp [tY]
@[scoped simp] theorem snd_tY : (tY W).snd = negfX W := by simp [tY]
@[scoped simp] theorem i₀_apply (k : K) : i₀ W k = TrivSqZeroExt.inl (algebraMap K (L W) k) := rfl

theorem algebraMap_K_A (k : K) : algebraMap K (A W) k = AdjoinRoot.mk _ (C (C k)) := rfl

theorem algebraMap_K_L (k : K) :
    algebraMap K (L W) k = algebraMap (A W) (L W) (AdjoinRoot.mk _ (C (C k))) := by
  rw [IsScalarTower.algebraMap_apply K (A W) (L W), algebraMap_K_A]

theorem fst_comp_Φ₀ :
    (fstRingHom W).comp (Φ₀ W) = (algebraMap (A W) (L W)).comp (AdjoinRoot.mk W.toAffine.polynomial) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  ·
    change (fstRingHom W).comp ((Φ₀ W).comp C) a = ((algebraMap (A W) (L W)).comp
      ((AdjoinRoot.mk W.toAffine.polynomial).comp C)) a
    congr 1
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp [Φ₀, algebraMap_K_L]
    · simp [Φ₀, x₀]
  · simp [Φ₀, y₀]

theorem fst_Φ₀ (g : K[X][Y]) : (Φ₀ W g).fst = algebraMap (A W) (L W) (AdjoinRoot.mk _ g) := by
  have := congrArg (fun f => f g) (fst_comp_Φ₀ W)
  simpa using this

theorem Φ₀_polynomial : Φ₀ W W.toAffine.polynomial = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_Φ₀, AdjoinRoot.mk_self, map_zero, TrivSqZeroExt.fst_zero]
  · simp only [Φ₀, WeierstrassCurve.Affine.polynomial, coe_eval₂RingHom, eval₂_add, eval₂_sub, eval₂_mul,
      eval₂_pow, eval₂_C, eval₂_X, TrivSqZeroExt.snd_zero]
    simp only [pow_succ, pow_zero, one_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_sub,
      fst_tX, snd_tX, fst_tY, snd_tY, i₀_apply, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, op_smul_eq_smul, smul_zero, zero_add, add_zero, mul_zero, zero_mul]
    simp only [fY, negfX]
    ring

noncomputable def φA : A W →+* T W :=
  AdjoinRoot.lift (eval₂RingHom (i₀ W) (tX W)) (tY W) (by
    have := Φ₀_polynomial W
    simpa [Φ₀] using this)

theorem φA_mk (g : K[X][Y]) : φA W (AdjoinRoot.mk _ g) = Φ₀ W g := by
  rw [φA, AdjoinRoot.lift_mk]; rfl

theorem fst_φA (a : A W) : (φA W a).fst = algebraMap (A W) (L W) a := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [φA_mk, fst_Φ₀]

theorem isUnit_φA (s : nonZeroDivisors (A W)) : IsUnit (φA W s) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_φA]
  exact IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2)

noncomputable def ΦL : L W →+* T W :=
  IsLocalization.lift (M := nonZeroDivisors (A W)) (isUnit_φA W)

theorem ΦL_algebraMap_A (a : A W) : ΦL W (algebraMap (A W) (L W) a) = φA W a :=
  IsLocalization.lift_eq _ _

theorem fst_ΦL (z : L W) : (ΦL W z).fst = z := by
  have h : (fstRingHom W).comp (ΦL W) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A W)) (RingHom.ext fun a => ?_)
    simp [ΦL_algebraMap_A, fst_φA]
  simpa using congrArg (fun f => f z) h

theorem ΦL_algebraMap (k : K) :
    ΦL W (algebraMap K (L W) k) = TrivSqZeroExt.inl (algebraMap K (L W) k) := by
  have : ΦL W (algebraMap K (L W) k) = Φ₀ W (C (C k)) := by
    rw [algebraMap_K_L, ΦL_algebraMap_A, φA_mk]
  rw [this]
  simp [Φ₀]

noncomputable def D : Derivation K (L W) (L W) where
  toFun z := (ΦL W z).snd
  map_add' a b := by simp
  map_smul' k a := by
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, fst_ΦL, fst_ΦL, ΦL_algebraMap,
      TrivSqZeroExt.snd_inl, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul]
  map_one_eq_zero' := by
    show (ΦL W 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  leibniz' a b := by
    show (ΦL W (a * b)).snd = a • (ΦL W b).snd + b • (ΦL W a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, fst_ΦL, fst_ΦL, op_smul_eq_smul]

theorem D_apply (z : L W) : D W z = (ΦL W z).snd := rfl

theorem D_x₀ : D W (x₀ W) = fY W := by
  rw [D_apply, x₀, ΦL_algebraMap_A, φA_mk]
  simp [Φ₀]

theorem D_y₀ : D W (y₀ W) = negfX W := by
  rw [D_apply, y₀, ΦL_algebraMap_A, φA_mk]
  simp [Φ₀]

noncomputable def evalHom : K[X][Y] →+* L W :=
  (algebraMap (A W) (L W)).comp (AdjoinRoot.mk W.toAffine.polynomial)

theorem evalHom_C_C (k : K) : evalHom W (C (C k)) = algebraMap K (L W) k := by
  rw [algebraMap_K_L]; rfl

theorem evalHom_C_X : evalHom W (C X) = x₀ W := rfl

theorem evalHom_Y : evalHom W Y = y₀ W := rfl

theorem evalEval_map_map (g : K[X][Y]) :
    (g.map (mapRingHom (algebraMap K (L W)))).evalEval (x₀ W) (y₀ W) = evalHom W g := by
  have : (evalEvalRingHom (x₀ W) (y₀ W)).comp (mapRingHom (mapRingHom (algebraMap K (L W))))
      = evalHom W := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change ((evalEvalRingHom (x₀ W) (y₀ W)).comp
          ((mapRingHom (mapRingHom (algebraMap K (L W)))).comp C)) a = ((evalHom W).comp C) a
      congr 1
      refine Polynomial.ringHom_ext (fun k => ?_) ?_
      · simp [evalHom_C_C]
      · simp [evalHom_C_X]
    · simp [evalHom_Y]
  simpa using congrArg (fun f => f g) this

theorem algebraMap_A_L_injective : Function.Injective (algebraMap (A W) (L W)) :=
  IsFractionRing.injective (A W) (L W)

theorem aeval_x₀_eq (g : K[X]) :
    Polynomial.aeval (x₀ W) g = algebraMap (A W) (L W) (AdjoinRoot.mk _ (C g)) := by
  have : (Polynomial.aeval (R := K) (x₀ W)).toRingHom = (evalHom W).comp C := by
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp [evalHom_C_C]
    · simp [evalHom_C_X]
  exact congrArg (fun f => f g) this

theorem aeval_x₀_injective :
    Function.Injective (Polynomial.aeval (R := K) (x₀ W) : K[X] →ₐ[K] L W) := by
  intro g₁ g₂ h
  rw [aeval_x₀_eq, aeval_x₀_eq] at h
  have h' := algebraMap_A_L_injective W h
  have hdeg : W.toAffine.polynomial.degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.degree_polynomial]; decide
  exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg h'

noncomputable abbrev EL : WeierstrassCurve (L W) := W.baseChange (L W)

theorem EL_polynomial :
    (EL W).toAffine.polynomial = W.toAffine.polynomial.map (mapRingHom (algebraMap K (L W))) := by
  simp [EL, baseChange, WeierstrassCurve.Affine.map_polynomial]

theorem equation_taut : (EL W).toAffine.Equation (x₀ W) (y₀ W) := by
  rw [WeierstrassCurve.Affine.Equation, EL_polynomial, evalEval_map_map, evalHom, RingHom.comp_apply,
    AdjoinRoot.mk_self, map_zero]

theorem fY_eq_evalHom :
    fY W = evalHom W (C (C 2) * Y + C (C W.a₁ * X + C W.a₃)) := by
  simp only [map_add, map_mul, evalHom_C_C, evalHom_C_X, evalHom_Y, fY, map_ofNat]
  ring

theorem fY_ne_zero (h2 : (2 : K) ≠ 0) : fY W ≠ 0 := by
  rw [fY_eq_evalHom, evalHom, RingHom.comp_apply]
  refine fun h => ?_
  have h0 := (algebraMap_A_L_injective W) (h.trans (map_zero _).symm)
  rw [AdjoinRoot.mk_eq_zero] at h0
  have ha : (C (2 : K) : K[X]) ≠ 0 := by rwa [Ne, C_eq_zero]
  have hg : (C (C (2 : K)) * Y + C (C W.a₁ * X + C W.a₃) : K[X][Y]).degree = 1 := degree_linear ha
  refine (WeierstrassCurve.Affine.monic_polynomial (W := W.toAffine)).not_dvd_of_degree_lt ?_ ?_ h0
  · intro h1
    rw [h1, degree_zero] at hg
    exact WithBot.bot_ne_one hg
  · rw [WeierstrassCurve.Affine.degree_polynomial, hg]
    exact WithBot.coe_lt_coe.mpr one_lt_two

theorem nonsingular_taut (h2 : (2 : K) ≠ 0) : (EL W).toAffine.Nonsingular (x₀ W) (y₀ W) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨equation_taut W, Or.inr ?_⟩
  exact fY_ne_zero W h2

noncomputable def P₀ (h2 : (2 : K) ≠ 0) : (EL W).toAffine.Point :=
  .some (x₀ W) (y₀ W) (nonsingular_taut W h2)

end InvariantDerivation
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
namespace S1Additivity
p2m_open "WeierstrassCurve"

theorem chord_dx {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ c₁ c₂ L dL x₃ y₃ : R)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hL : L * (x₁ - x₂) = y₁ - y₂)
    (hdL : dL * (x₁ - x₂)
      = (c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - c₂ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂))
        - L * (c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃)))
    (hx₃ : x₃ = L ^ 2 + a₁ * L - a₂ - x₁ - x₂)
    (hy₃ : y₃ = -(L * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    (x₁ - x₂) ^ 4 * (((2 * L + a₁) * dL - c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃))
      - (c₁ + c₂) * (2 * y₃ + a₁ * x₃ + a₃)) = 0 := by
  subst hx₃ hy₃
  linear_combination (2*L*x₁^3 - 6*L*x₁^2*x₂ + 6*L*x₁*x₂^2 - 2*L*x₂^3 + a₁*x₁^3 - 3*a₁*x₁^2*x₂ + 3*a₁*x₁*x₂^2 -
      a₁*x₂^3) * hdL
    + (2*L^2*c₁*x₁^3 - 6*L^2*c₁*x₁^2*x₂ + 6*L^2*c₁*x₁*x₂^2 - 2*L^2*c₁*x₂^3 + 2*L^2*c₂*x₁^3 -
      6*L^2*c₂*x₁^2*x₂ + 6*L^2*c₂*x₁*x₂^2 - 2*L^2*c₂*x₂^3 + L*a₁*c₁*x₁^3 - 5*L*a₁*c₁*x₁^2*x₂ +
      7*L*a₁*c₁*x₁*x₂^2 - 3*L*a₁*c₁*x₂^3 + 3*L*a₁*c₂*x₁^3 - 7*L*a₁*c₂*x₁^2*x₂ + 5*L*a₁*c₂*x₁*x₂^2 -
      L*a₁*c₂*x₂^3 - 2*L*a₃*c₁*x₁^2 + 4*L*a₃*c₁*x₁*x₂ - 2*L*a₃*c₁*x₂^2 + 2*L*a₃*c₂*x₁^2 -
      4*L*a₃*c₂*x₁*x₂ + 2*L*a₃*c₂*x₂^2 - 2*L*c₁*x₁^2*y₁ - 2*L*c₁*x₁^2*y₂ + 4*L*c₁*x₁*x₂*y₁ +
      4*L*c₁*x₁*x₂*y₂ - 2*L*c₁*x₂^2*y₁ - 2*L*c₁*x₂^2*y₂ + 2*L*c₂*x₁^2*y₁ + 2*L*c₂*x₁^2*y₂ -
      4*L*c₂*x₁*x₂*y₁ - 4*L*c₂*x₁*x₂*y₂ + 2*L*c₂*x₂^2*y₁ + 2*L*c₂*x₂^2*y₂ - a₁^2*c₁*x₁^2*x₂ +
      2*a₁^2*c₁*x₁*x₂^2 - a₁^2*c₁*x₂^3 + a₁^2*c₂*x₁^3 - 2*a₁^2*c₂*x₁^2*x₂ + a₁^2*c₂*x₁*x₂^2 -
      a₁*a₃*c₁*x₁^2 + 2*a₁*a₃*c₁*x₁*x₂ - a₁*a₃*c₁*x₂^2 + a₁*a₃*c₂*x₁^2 - 2*a₁*a₃*c₂*x₁*x₂ +
      a₁*a₃*c₂*x₂^2 - 3*a₁*c₁*x₁^2*y₁ - a₁*c₁*x₁^2*y₂ + 4*a₁*c₁*x₁*x₂*y₁ + 4*a₁*c₁*x₁*x₂*y₂ -
      a₁*c₁*x₂^2*y₁ - 3*a₁*c₁*x₂^2*y₂ + 3*a₁*c₂*x₁^2*y₁ + a₁*c₂*x₁^2*y₂ - 4*a₁*c₂*x₁*x₂*y₁ -
      4*a₁*c₂*x₁*x₂*y₂ + a₁*c₂*x₂^2*y₁ + 3*a₁*c₂*x₂^2*y₂ + 2*a₂*c₁*x₁^3 - 2*a₂*c₁*x₁^2*x₂ -
      2*a₂*c₁*x₁*x₂^2 + 2*a₂*c₁*x₂^3 - 2*a₂*c₂*x₁^3 + 2*a₂*c₂*x₁^2*x₂ + 2*a₂*c₂*x₁*x₂^2 -
      2*a₂*c₂*x₂^3 - 2*a₃*c₁*x₁*y₁ + 2*a₃*c₁*x₁*y₂ + 2*a₃*c₁*x₂*y₁ - 2*a₃*c₁*x₂*y₂ + 2*a₃*c₂*x₁*y₁ -
      2*a₃*c₂*x₁*y₂ - 2*a₃*c₂*x₂*y₁ + 2*a₃*c₂*x₂*y₂ + 2*a₄*c₁*x₁^2 - 4*a₄*c₁*x₁*x₂ + 2*a₄*c₁*x₂^2 -
      2*a₄*c₂*x₁^2 + 4*a₄*c₂*x₁*x₂ - 2*a₄*c₂*x₂^2 + 2*c₁*x₁^4 - 2*c₁*x₁^3*x₂ - 2*c₁*x₁*x₂^3 -
      2*c₁*x₁*y₁^2 + 2*c₁*x₁*y₂^2 + 2*c₁*x₂^4 + 2*c₁*x₂*y₁^2 - 2*c₁*x₂*y₂^2 - 4*c₂*x₁^4 +
      10*c₂*x₁^3*x₂ - 12*c₂*x₁^2*x₂^2 + 10*c₂*x₁*x₂^3 + 2*c₂*x₁*y₁^2 - 2*c₂*x₁*y₂^2 - 4*c₂*x₂^4 -
      2*c₂*x₂*y₁^2 + 2*c₂*x₂*y₂^2) * hL
    + (-a₁*c₁*x₁^2 + 2*a₁*c₁*x₁*x₂ - a₁*c₁*x₂^2 + a₁*c₂*x₁^2 - 2*a₁*c₂*x₁*x₂ + a₁*c₂*x₂^2 - 2*c₁*x₁*y₁
      + 2*c₁*x₁*y₂ + 2*c₁*x₂*y₁ - 2*c₁*x₂*y₂ + 2*c₂*x₁*y₁ - 2*c₂*x₁*y₂ - 2*c₂*x₂*y₁ + 2*c₂*x₂*y₂) * h₁
    + (a₁*c₁*x₁^2 - 2*a₁*c₁*x₁*x₂ + a₁*c₁*x₂^2 - a₁*c₂*x₁^2 + 2*a₁*c₂*x₁*x₂ - a₁*c₂*x₂^2 + 2*c₁*x₁*y₁
      - 2*c₁*x₁*y₂ - 2*c₁*x₂*y₁ + 2*c₁*x₂*y₂ - 2*c₂*x₁*y₁ + 2*c₂*x₁*y₂ + 2*c₂*x₂*y₁ - 2*c₂*x₂*y₂) * h₂

theorem chord_dy {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ c₁ c₂ L dL x₃ y₃ : R)
    (h₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (h₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hL : L * (x₁ - x₂) = y₁ - y₂)
    (hdL : dL * (x₁ - x₂)
      = (c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - c₂ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂))
        - L * (c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃)))
    (hx₃ : x₃ = L ^ 2 + a₁ * L - a₂ - x₁ - x₂)
    (hy₃ : y₃ = -(L * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    (x₁ - x₂) ^ 5 * ((-(dL * (x₃ - x₁) + L * (((2 * L + a₁) * dL - c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃)) - c₁ * (2 * y₁ + a₁ * x₁ + a₃)) + c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)) - a₁ * ((2 * L + a₁) * dL - c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃)))
      - (c₁ + c₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃)) = 0 := by
  subst hx₃ hy₃
  linear_combination (-3*L^2*x₁^4 + 12*L^2*x₁^3*x₂ - 18*L^2*x₁^2*x₂^2 + 12*L^2*x₁*x₂^3 - 3*L^2*x₂^4 - 4*L*a₁*x₁^4 +
      16*L*a₁*x₁^3*x₂ - 24*L*a₁*x₁^2*x₂^2 + 16*L*a₁*x₁*x₂^3 - 4*L*a₁*x₂^4 - a₁^2*x₁^4 +
      4*a₁^2*x₁^3*x₂ - 6*a₁^2*x₁^2*x₂^2 + 4*a₁^2*x₁*x₂^3 - a₁^2*x₂^4 + a₂*x₁^4 - 4*a₂*x₁^3*x₂ +
      6*a₂*x₁^2*x₂^2 - 4*a₂*x₁*x₂^3 + a₂*x₂^4 + 2*x₁^5 - 7*x₁^4*x₂ + 8*x₁^3*x₂^2 - 2*x₁^2*x₂^3 -
      2*x₁*x₂^4 + x₂^5) * hdL
    + (-3*L^3*c₁*x₁^4 + 12*L^3*c₁*x₁^3*x₂ - 18*L^3*c₁*x₁^2*x₂^2 + 12*L^3*c₁*x₁*x₂^3 - 3*L^3*c₁*x₂^4 -
      3*L^3*c₂*x₁^4 + 12*L^3*c₂*x₁^3*x₂ - 18*L^3*c₂*x₁^2*x₂^2 + 12*L^3*c₂*x₁*x₂^3 - 3*L^3*c₂*x₂^4 -
      4*L^2*a₁*c₁*x₁^4 + 19*L^2*a₁*c₁*x₁^3*x₂ - 33*L^2*a₁*c₁*x₁^2*x₂^2 + 25*L^2*a₁*c₁*x₁*x₂^3 -
      7*L^2*a₁*c₁*x₂^4 - 7*L^2*a₁*c₂*x₁^4 + 25*L^2*a₁*c₂*x₁^3*x₂ - 33*L^2*a₁*c₂*x₁^2*x₂^2 +
      19*L^2*a₁*c₂*x₁*x₂^3 - 4*L^2*a₁*c₂*x₂^4 + 3*L^2*a₃*c₁*x₁^3 - 9*L^2*a₃*c₁*x₁^2*x₂ +
      9*L^2*a₃*c₁*x₁*x₂^2 - 3*L^2*a₃*c₁*x₂^3 - 3*L^2*a₃*c₂*x₁^3 + 9*L^2*a₃*c₂*x₁^2*x₂ -
      9*L^2*a₃*c₂*x₁*x₂^2 + 3*L^2*a₃*c₂*x₂^3 + 3*L^2*c₁*x₁^3*y₁ + 3*L^2*c₁*x₁^3*y₂ -
      9*L^2*c₁*x₁^2*x₂*y₁ - 9*L^2*c₁*x₁^2*x₂*y₂ + 9*L^2*c₁*x₁*x₂^2*y₁ + 9*L^2*c₁*x₁*x₂^2*y₂ -
      3*L^2*c₁*x₂^3*y₁ - 3*L^2*c₁*x₂^3*y₂ - 3*L^2*c₂*x₁^3*y₁ - 3*L^2*c₂*x₁^3*y₂ + 9*L^2*c₂*x₁^2*x₂*y₁
      + 9*L^2*c₂*x₁^2*x₂*y₂ - 9*L^2*c₂*x₁*x₂^2*y₁ - 9*L^2*c₂*x₁*x₂^2*y₂ + 3*L^2*c₂*x₂^3*y₁ +
      3*L^2*c₂*x₂^3*y₂ - L*a₁^2*c₁*x₁^4 + 8*L*a₁^2*c₁*x₁^3*x₂ - 18*L*a₁^2*c₁*x₁^2*x₂^2 +
      16*L*a₁^2*c₁*x₁*x₂^3 - 5*L*a₁^2*c₁*x₂^4 - 5*L*a₁^2*c₂*x₁^4 + 16*L*a₁^2*c₂*x₁^3*x₂ -
      18*L*a₁^2*c₂*x₁^2*x₂^2 + 8*L*a₁^2*c₂*x₁*x₂^3 - L*a₁^2*c₂*x₂^4 + 4*L*a₁*a₃*c₁*x₁^3 -
      12*L*a₁*a₃*c₁*x₁^2*x₂ + 12*L*a₁*a₃*c₁*x₁*x₂^2 - 4*L*a₁*a₃*c₁*x₂^3 - 4*L*a₁*a₃*c₂*x₁^3 +
      12*L*a₁*a₃*c₂*x₁^2*x₂ - 12*L*a₁*a₃*c₂*x₁*x₂^2 + 4*L*a₁*a₃*c₂*x₂^3 + 7*L*a₁*c₁*x₁^3*y₁ +
      4*L*a₁*c₁*x₁^3*y₂ - 18*L*a₁*c₁*x₁^2*x₂*y₁ - 15*L*a₁*c₁*x₁^2*x₂*y₂ + 15*L*a₁*c₁*x₁*x₂^2*y₁ +
      18*L*a₁*c₁*x₁*x₂^2*y₂ - 4*L*a₁*c₁*x₂^3*y₁ - 7*L*a₁*c₁*x₂^3*y₂ - 7*L*a₁*c₂*x₁^3*y₁ -
      4*L*a₁*c₂*x₁^3*y₂ + 18*L*a₁*c₂*x₁^2*x₂*y₁ + 15*L*a₁*c₂*x₁^2*x₂*y₂ - 15*L*a₁*c₂*x₁*x₂^2*y₁ -
      18*L*a₁*c₂*x₁*x₂^2*y₂ + 4*L*a₁*c₂*x₂^3*y₁ + 7*L*a₁*c₂*x₂^3*y₂ - 2*L*a₂*c₁*x₁^4 +
      2*L*a₂*c₁*x₁^3*x₂ + 6*L*a₂*c₁*x₁^2*x₂^2 - 10*L*a₂*c₁*x₁*x₂^3 + 4*L*a₂*c₁*x₂^4 + 4*L*a₂*c₂*x₁^4
      - 10*L*a₂*c₂*x₁^3*x₂ + 6*L*a₂*c₂*x₁^2*x₂^2 + 2*L*a₂*c₂*x₁*x₂^3 - 2*L*a₂*c₂*x₂^4 +
      3*L*a₃*c₁*x₁^2*y₁ - 3*L*a₃*c₁*x₁^2*y₂ - 6*L*a₃*c₁*x₁*x₂*y₁ + 6*L*a₃*c₁*x₁*x₂*y₂ +
      3*L*a₃*c₁*x₂^2*y₁ - 3*L*a₃*c₁*x₂^2*y₂ - 3*L*a₃*c₂*x₁^2*y₁ + 3*L*a₃*c₂*x₁^2*y₂ +
      6*L*a₃*c₂*x₁*x₂*y₁ - 6*L*a₃*c₂*x₁*x₂*y₂ - 3*L*a₃*c₂*x₂^2*y₁ + 3*L*a₃*c₂*x₂^2*y₂ -
      3*L*a₄*c₁*x₁^3 + 9*L*a₄*c₁*x₁^2*x₂ - 9*L*a₄*c₁*x₁*x₂^2 + 3*L*a₄*c₁*x₂^3 + 3*L*a₄*c₂*x₁^3 -
      9*L*a₄*c₂*x₁^2*x₂ + 9*L*a₄*c₂*x₁*x₂^2 - 3*L*a₄*c₂*x₂^3 - 3*L*c₁*x₁^5 + 9*L*c₁*x₁^4*x₂ -
      15*L*c₁*x₁^3*x₂^2 + 21*L*c₁*x₁^2*x₂^3 + 3*L*c₁*x₁^2*y₁^2 - 3*L*c₁*x₁^2*y₂^2 - 18*L*c₁*x₁*x₂^4 -
      6*L*c₁*x₁*x₂*y₁^2 + 6*L*c₁*x₁*x₂*y₂^2 + 6*L*c₁*x₂^5 + 3*L*c₁*x₂^2*y₁^2 - 3*L*c₁*x₂^2*y₂^2 +
      6*L*c₂*x₁^5 - 18*L*c₂*x₁^4*x₂ + 21*L*c₂*x₁^3*x₂^2 - 15*L*c₂*x₁^2*x₂^3 - 3*L*c₂*x₁^2*y₁^2 +
      3*L*c₂*x₁^2*y₂^2 + 9*L*c₂*x₁*x₂^4 + 6*L*c₂*x₁*x₂*y₁^2 - 6*L*c₂*x₁*x₂*y₂^2 - 3*L*c₂*x₂^5 -
      3*L*c₂*x₂^2*y₁^2 + 3*L*c₂*x₂^2*y₂^2 + a₁^3*c₁*x₁^3*x₂ - 3*a₁^3*c₁*x₁^2*x₂^2 + 3*a₁^3*c₁*x₁*x₂^3
      - a₁^3*c₁*x₂^4 - a₁^3*c₂*x₁^4 + 3*a₁^3*c₂*x₁^3*x₂ - 3*a₁^3*c₂*x₁^2*x₂^2 + a₁^3*c₂*x₁*x₂^3 +
      a₁^2*a₃*c₁*x₁^3 - 3*a₁^2*a₃*c₁*x₁^2*x₂ + 3*a₁^2*a₃*c₁*x₁*x₂^2 - a₁^2*a₃*c₁*x₂^3 -
      a₁^2*a₃*c₂*x₁^3 + 3*a₁^2*a₃*c₂*x₁^2*x₂ - 3*a₁^2*a₃*c₂*x₁*x₂^2 + a₁^2*a₃*c₂*x₂^3 +
      5*a₁^2*c₁*x₁^3*y₁ + a₁^2*c₁*x₁^3*y₂ - 11*a₁^2*c₁*x₁^2*x₂*y₁ - 7*a₁^2*c₁*x₁^2*x₂*y₂ +
      7*a₁^2*c₁*x₁*x₂^2*y₁ + 11*a₁^2*c₁*x₁*x₂^2*y₂ - a₁^2*c₁*x₂^3*y₁ - 5*a₁^2*c₁*x₂^3*y₂ -
      5*a₁^2*c₂*x₁^3*y₁ - a₁^2*c₂*x₁^3*y₂ + 11*a₁^2*c₂*x₁^2*x₂*y₁ + 7*a₁^2*c₂*x₁^2*x₂*y₂ -
      7*a₁^2*c₂*x₁*x₂^2*y₁ - 11*a₁^2*c₂*x₁*x₂^2*y₂ + a₁^2*c₂*x₂^3*y₁ + 5*a₁^2*c₂*x₂^3*y₂ -
      4*a₁*a₂*c₁*x₁^4 + 7*a₁*a₂*c₁*x₁^3*x₂ + 3*a₁*a₂*c₁*x₁^2*x₂^2 - 11*a₁*a₂*c₁*x₁*x₂^3 +
      5*a₁*a₂*c₁*x₂^4 + 5*a₁*a₂*c₂*x₁^4 - 11*a₁*a₂*c₂*x₁^3*x₂ + 3*a₁*a₂*c₂*x₁^2*x₂^2 +
      7*a₁*a₂*c₂*x₁*x₂^3 - 4*a₁*a₂*c₂*x₂^4 + 4*a₁*a₃*c₁*x₁^2*y₁ - 4*a₁*a₃*c₁*x₁^2*y₂ -
      8*a₁*a₃*c₁*x₁*x₂*y₁ + 8*a₁*a₃*c₁*x₁*x₂*y₂ + 4*a₁*a₃*c₁*x₂^2*y₁ - 4*a₁*a₃*c₁*x₂^2*y₂ -
      4*a₁*a₃*c₂*x₁^2*y₁ + 4*a₁*a₃*c₂*x₁^2*y₂ + 8*a₁*a₃*c₂*x₁*x₂*y₁ - 8*a₁*a₃*c₂*x₁*x₂*y₂ -
      4*a₁*a₃*c₂*x₂^2*y₁ + 4*a₁*a₃*c₂*x₂^2*y₂ - 4*a₁*a₄*c₁*x₁^3 + 12*a₁*a₄*c₁*x₁^2*x₂ -
      12*a₁*a₄*c₁*x₁*x₂^2 + 4*a₁*a₄*c₁*x₂^3 + 4*a₁*a₄*c₂*x₁^3 - 12*a₁*a₄*c₂*x₁^2*x₂ +
      12*a₁*a₄*c₂*x₁*x₂^2 - 4*a₁*a₄*c₂*x₂^3 - 4*a₁*c₁*x₁^5 + 8*a₁*c₁*x₁^4*x₂ - 7*a₁*c₁*x₁^3*x₂^2 +
      13*a₁*c₁*x₁^2*x₂^3 + 7*a₁*c₁*x₁^2*y₁^2 - 3*a₁*c₁*x₁^2*y₁*y₂ - 4*a₁*c₁*x₁^2*y₂^2 -
      17*a₁*c₁*x₁*x₂^4 - 11*a₁*c₁*x₁*x₂*y₁^2 + 11*a₁*c₁*x₁*x₂*y₂^2 + 7*a₁*c₁*x₂^5 + 4*a₁*c₁*x₂^2*y₁^2
      + 3*a₁*c₁*x₂^2*y₁*y₂ - 7*a₁*c₁*x₂^2*y₂^2 + 8*a₁*c₂*x₁^5 - 22*a₁*c₂*x₁^4*x₂ + 23*a₁*c₂*x₁^3*x₂^2
      - 17*a₁*c₂*x₁^2*x₂^3 - 7*a₁*c₂*x₁^2*y₁^2 + 3*a₁*c₂*x₁^2*y₁*y₂ + 4*a₁*c₂*x₁^2*y₂^2 +
      13*a₁*c₂*x₁*x₂^4 + 11*a₁*c₂*x₁*x₂*y₁^2 - 11*a₁*c₂*x₁*x₂*y₂^2 - 5*a₁*c₂*x₂^5 - 4*a₁*c₂*x₂^2*y₁^2
      - 3*a₁*c₂*x₂^2*y₁*y₂ + 7*a₁*c₂*x₂^2*y₂^2 - a₂*a₃*c₁*x₁^3 + 3*a₂*a₃*c₁*x₁^2*x₂ -
      3*a₂*a₃*c₁*x₁*x₂^2 + a₂*a₃*c₁*x₂^3 + a₂*a₃*c₂*x₁^3 - 3*a₂*a₃*c₂*x₁^2*x₂ + 3*a₂*a₃*c₂*x₁*x₂^2 -
      a₂*a₃*c₂*x₂^3 - 4*a₂*c₁*x₁^3*y₁ + 2*a₂*c₁*x₁^3*y₂ + 6*a₂*c₁*x₁^2*x₂*y₁ - 6*a₂*c₁*x₁*x₂^2*y₂ -
      2*a₂*c₁*x₂^3*y₁ + 4*a₂*c₁*x₂^3*y₂ + 4*a₂*c₂*x₁^3*y₁ - 2*a₂*c₂*x₁^3*y₂ - 6*a₂*c₂*x₁^2*x₂*y₁ +
      6*a₂*c₂*x₁*x₂^2*y₂ + 2*a₂*c₂*x₂^3*y₁ - 4*a₂*c₂*x₂^3*y₂ - 3*a₃*c₁*x₁^3*x₂ + 9*a₃*c₁*x₁^2*x₂^2 -
      9*a₃*c₁*x₁*x₂^3 + 3*a₃*c₁*x₁*y₁^2 - 6*a₃*c₁*x₁*y₁*y₂ + 3*a₃*c₁*x₁*y₂^2 + 3*a₃*c₁*x₂^4 -
      3*a₃*c₁*x₂*y₁^2 + 6*a₃*c₁*x₂*y₁*y₂ - 3*a₃*c₁*x₂*y₂^2 + 3*a₃*c₂*x₁^4 - 9*a₃*c₂*x₁^3*x₂ +
      9*a₃*c₂*x₁^2*x₂^2 - 3*a₃*c₂*x₁*x₂^3 - 3*a₃*c₂*x₁*y₁^2 + 6*a₃*c₂*x₁*y₁*y₂ - 3*a₃*c₂*x₁*y₂^2 +
      3*a₃*c₂*x₂*y₁^2 - 6*a₃*c₂*x₂*y₁*y₂ + 3*a₃*c₂*x₂*y₂^2 - 3*a₄*c₁*x₁^2*y₁ + 3*a₄*c₁*x₁^2*y₂ +
      6*a₄*c₁*x₁*x₂*y₁ - 6*a₄*c₁*x₁*x₂*y₂ - 3*a₄*c₁*x₂^2*y₁ + 3*a₄*c₁*x₂^2*y₂ + 3*a₄*c₂*x₁^2*y₁ -
      3*a₄*c₂*x₁^2*y₂ - 6*a₄*c₂*x₁*x₂*y₁ + 6*a₄*c₂*x₁*x₂*y₂ + 3*a₄*c₂*x₂^2*y₁ - 3*a₄*c₂*x₂^2*y₂ -
      3*c₁*x₁^4*y₁ + 3*c₁*x₁^4*y₂ - 6*c₁*x₁^3*x₂*y₂ + 9*c₁*x₁^2*x₂^2*y₁ + 9*c₁*x₁^2*x₂^2*y₂ -
      6*c₁*x₁*x₂^3*y₁ - 12*c₁*x₁*x₂^3*y₂ + 3*c₁*x₁*y₁^3 - 3*c₁*x₁*y₁^2*y₂ - 3*c₁*x₁*y₁*y₂^2 +
      3*c₁*x₁*y₂^3 + 6*c₁*x₂^4*y₂ - 3*c₁*x₂*y₁^3 + 3*c₁*x₂*y₁^2*y₂ + 3*c₁*x₂*y₁*y₂^2 - 3*c₁*x₂*y₂^3 +
      6*c₂*x₁^4*y₁ - 12*c₂*x₁^3*x₂*y₁ - 6*c₂*x₁^3*x₂*y₂ + 9*c₂*x₁^2*x₂^2*y₁ + 9*c₂*x₁^2*x₂^2*y₂ -
      6*c₂*x₁*x₂^3*y₁ - 3*c₂*x₁*y₁^3 + 3*c₂*x₁*y₁^2*y₂ + 3*c₂*x₁*y₁*y₂^2 - 3*c₂*x₁*y₂^3 +
      3*c₂*x₂^4*y₁ - 3*c₂*x₂^4*y₂ + 3*c₂*x₂*y₁^3 - 3*c₂*x₂*y₁^2*y₂ - 3*c₂*x₂*y₁*y₂^2 + 3*c₂*x₂*y₂^3) * hL
    + (a₁^2*c₁*x₁^3 - 3*a₁^2*c₁*x₁^2*x₂ + 3*a₁^2*c₁*x₁*x₂^2 - a₁^2*c₁*x₂^3 - a₁^2*c₂*x₁^3 +
      3*a₁^2*c₂*x₁^2*x₂ - 3*a₁^2*c₂*x₁*x₂^2 + a₁^2*c₂*x₂^3 + 4*a₁*c₁*x₁^2*y₁ - 4*a₁*c₁*x₁^2*y₂ -
      8*a₁*c₁*x₁*x₂*y₁ + 5*a₁*c₁*x₁*x₂*y₂ + 4*a₁*c₁*x₂^2*y₁ - a₁*c₁*x₂^2*y₂ - 4*a₁*c₂*x₁^2*y₁ +
      4*a₁*c₂*x₁^2*y₂ + 8*a₁*c₂*x₁*x₂*y₁ - 5*a₁*c₂*x₁*x₂*y₂ - 4*a₁*c₂*x₂^2*y₁ + a₁*c₂*x₂^2*y₂ -
      a₂*c₁*x₁^3 + 3*a₂*c₁*x₁^2*x₂ - 2*a₂*c₁*x₂^3 + a₂*c₂*x₁^3 - 3*a₂*c₂*x₁^2*x₂ + 2*a₂*c₂*x₂^3 -
      3*a₃*c₁*x₁*y₂ + 3*a₃*c₁*x₂*y₂ + 3*a₃*c₂*x₁*y₂ - 3*a₃*c₂*x₂*y₂ + 3*a₄*c₁*x₁*x₂ - 3*a₄*c₁*x₂^2 -
      3*a₄*c₂*x₁*x₂ + 3*a₄*c₂*x₂^2 + 3*a₆*c₁*x₁ - 3*a₆*c₁*x₂ - 3*a₆*c₂*x₁ + 3*a₆*c₂*x₂ - 3*c₁*x₁^3*x₂
      + 9*c₁*x₁^2*x₂^2 - 6*c₁*x₁*x₂^3 + 3*c₁*x₁*y₁^2 - 6*c₁*x₁*y₁*y₂ - 3*c₁*x₂*y₁^2 + 6*c₁*x₂*y₁*y₂ +
      3*c₂*x₁^4 - 9*c₂*x₁^3*x₂ + 9*c₂*x₁^2*x₂^2 - 6*c₂*x₁*x₂^3 - 3*c₂*x₁*y₁^2 + 6*c₂*x₁*y₁*y₂ +
      3*c₂*x₂^4 + 3*c₂*x₂*y₁^2 - 6*c₂*x₂*y₁*y₂) * h₁
    + (-a₁^2*c₁*x₁^3 + 3*a₁^2*c₁*x₁^2*x₂ - 3*a₁^2*c₁*x₁*x₂^2 + a₁^2*c₁*x₂^3 + a₁^2*c₂*x₁^3 -
      3*a₁^2*c₂*x₁^2*x₂ + 3*a₁^2*c₂*x₁*x₂^2 - a₁^2*c₂*x₂^3 - a₁*c₁*x₁^2*y₁ + 4*a₁*c₁*x₁^2*y₂ +
      5*a₁*c₁*x₁*x₂*y₁ - 8*a₁*c₁*x₁*x₂*y₂ - 4*a₁*c₁*x₂^2*y₁ + 4*a₁*c₁*x₂^2*y₂ + a₁*c₂*x₁^2*y₁ -
      4*a₁*c₂*x₁^2*y₂ - 5*a₁*c₂*x₁*x₂*y₁ + 8*a₁*c₂*x₁*x₂*y₂ + 4*a₁*c₂*x₂^2*y₁ - 4*a₁*c₂*x₂^2*y₂ -
      2*a₂*c₁*x₁^3 + 3*a₂*c₁*x₁*x₂^2 - a₂*c₁*x₂^3 + 2*a₂*c₂*x₁^3 - 3*a₂*c₂*x₁*x₂^2 + a₂*c₂*x₂^3 +
      3*a₃*c₁*x₁*y₁ - 3*a₃*c₁*x₂*y₁ - 3*a₃*c₂*x₁*y₁ + 3*a₃*c₂*x₂*y₁ - 3*a₄*c₁*x₁^2 + 3*a₄*c₁*x₁*x₂ +
      3*a₄*c₂*x₁^2 - 3*a₄*c₂*x₁*x₂ - 3*a₆*c₁*x₁ + 3*a₆*c₁*x₂ + 3*a₆*c₂*x₁ - 3*a₆*c₂*x₂ - 3*c₁*x₁^4 +
      6*c₁*x₁^3*x₂ - 9*c₁*x₁^2*x₂^2 + 9*c₁*x₁*x₂^3 + 6*c₁*x₁*y₁*y₂ - 3*c₁*x₁*y₂^2 - 3*c₁*x₂^4 -
      6*c₁*x₂*y₁*y₂ + 3*c₁*x₂*y₂^2 + 6*c₂*x₁^3*x₂ - 9*c₂*x₁^2*x₂^2 + 3*c₂*x₁*x₂^3 - 6*c₂*x₁*y₁*y₂ +
      3*c₂*x₁*y₂^2 + 6*c₂*x₂*y₁*y₂ - 3*c₂*x₂*y₂^2) * h₂

theorem tangent_dx {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x y c L dL x₃ y₃ : R)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hL : L * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hdL : dL * (2 * y + a₁ * x + a₃)
      = (6 * x + 2 * a₂) * (c * (2 * y + a₁ * x + a₃)) - a₁ * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y))
        - L * (2 * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) + a₁ * (c * (2 * y + a₁ * x + a₃))))
    (hx₃ : x₃ = L ^ 2 + a₁ * L - a₂ - x - x)
    (hy₃ : y₃ = -(L * (x₃ - x) + y) - a₁ * x₃ - a₃) :
    (2 * y + a₁ * x + a₃) ^ 4 * (((2 * L + a₁) * dL - c * (2 * y + a₁ * x + a₃) - c * (2 * y + a₁ * x + a₃))
      - (c + c) * (2 * y₃ + a₁ * x₃ + a₃)) = 0 := by
  subst hx₃ hy₃
  linear_combination (2*L*a₁^3*x^3 + 6*L*a₁^2*a₃*x^2 + 12*L*a₁^2*x^2*y + 6*L*a₁*a₃^2*x + 24*L*a₁*a₃*x*y +
      24*L*a₁*x*y^2 + 2*L*a₃^3 + 12*L*a₃^2*y + 24*L*a₃*y^2 + 16*L*y^3 + a₁^4*x^3 + 3*a₁^3*a₃*x^2 +
      6*a₁^3*x^2*y + 3*a₁^2*a₃^2*x + 12*a₁^2*a₃*x*y + 12*a₁^2*x*y^2 + a₁*a₃^3 + 6*a₁*a₃^2*y +
      12*a₁*a₃*y^2 + 8*a₁*y^3) * hdL
    + (4*L^2*a₁^3*c*x^3 + 12*L^2*a₁^2*a₃*c*x^2 + 24*L^2*a₁^2*c*x^2*y + 12*L^2*a₁*a₃^2*c*x +
      48*L^2*a₁*a₃*c*x*y + 48*L^2*a₁*c*x*y^2 + 4*L^2*a₃^3*c + 24*L^2*a₃^2*c*y + 48*L^2*a₃*c*y^2 +
      32*L^2*c*y^3 + 4*L*a₁^4*c*x^3 + 12*L*a₁^3*a₃*c*x^2 + 24*L*a₁^3*c*x^2*y + 12*L*a₁^2*a₃^2*c*x +
      48*L*a₁^2*a₃*c*x*y + 48*L*a₁^2*c*x*y^2 + 4*L*a₁*a₃^3*c + 24*L*a₁*a₃^2*c*y + 48*L*a₁*a₃*c*y^2 +
      32*L*a₁*c*y^3 + a₁^5*c*x^3 + 3*a₁^4*a₃*c*x^2 + 6*a₁^4*c*x^2*y + 3*a₁^3*a₃^2*c*x +
      12*a₁^3*a₃*c*x*y + 12*a₁^3*c*x*y^2 + a₁^2*a₃^3*c + 6*a₁^2*a₃^2*c*y + 12*a₁^2*a₃*c*y^2 +
      8*a₁^2*c*y^3) * hL
    + (0) * h

theorem tangent_dy {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ x y c L dL x₃ y₃ : R)
    (h : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hL : L * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hdL : dL * (2 * y + a₁ * x + a₃)
      = (6 * x + 2 * a₂) * (c * (2 * y + a₁ * x + a₃)) - a₁ * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y))
        - L * (2 * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) + a₁ * (c * (2 * y + a₁ * x + a₃))))
    (hx₃ : x₃ = L ^ 2 + a₁ * L - a₂ - x - x)
    (hy₃ : y₃ = -(L * (x₃ - x) + y) - a₁ * x₃ - a₃) :
    (2 * y + a₁ * x + a₃) ^ 5 * ((-(dL * (x₃ - x) + L * (((2 * L + a₁) * dL - c * (2 * y + a₁ * x + a₃) - c * (2 * y + a₁ * x + a₃)) - c * (2 * y + a₁ * x + a₃)) + c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) - a₁ * ((2 * L + a₁) * dL - c * (2 * y + a₁ * x + a₃) - c * (2 * y + a₁ * x + a₃)))
      - (c + c) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃)) = 0 := by
  subst hx₃ hy₃
  linear_combination (-3*L^2*a₁^4*x^4 - 12*L^2*a₁^3*a₃*x^3 - 24*L^2*a₁^3*x^3*y - 18*L^2*a₁^2*a₃^2*x^2 -
      72*L^2*a₁^2*a₃*x^2*y - 72*L^2*a₁^2*x^2*y^2 - 12*L^2*a₁*a₃^3*x - 72*L^2*a₁*a₃^2*x*y -
      144*L^2*a₁*a₃*x*y^2 - 96*L^2*a₁*x*y^3 - 3*L^2*a₃^4 - 24*L^2*a₃^3*y - 72*L^2*a₃^2*y^2 -
      96*L^2*a₃*y^3 - 48*L^2*y^4 - 4*L*a₁^5*x^4 - 16*L*a₁^4*a₃*x^3 - 32*L*a₁^4*x^3*y -
      24*L*a₁^3*a₃^2*x^2 - 96*L*a₁^3*a₃*x^2*y - 96*L*a₁^3*x^2*y^2 - 16*L*a₁^2*a₃^3*x -
      96*L*a₁^2*a₃^2*x*y - 192*L*a₁^2*a₃*x*y^2 - 128*L*a₁^2*x*y^3 - 4*L*a₁*a₃^4 - 32*L*a₁*a₃^3*y -
      96*L*a₁*a₃^2*y^2 - 128*L*a₁*a₃*y^3 - 64*L*a₁*y^4 - a₁^6*x^4 - 4*a₁^5*a₃*x^3 - 8*a₁^5*x^3*y +
      a₁^4*a₂*x^4 - 6*a₁^4*a₃^2*x^2 - 24*a₁^4*a₃*x^2*y + 3*a₁^4*x^5 - 24*a₁^4*x^2*y^2 +
      4*a₁^3*a₂*a₃*x^3 + 8*a₁^3*a₂*x^3*y - 4*a₁^3*a₃^3*x - 24*a₁^3*a₃^2*x*y + 12*a₁^3*a₃*x^4 -
      48*a₁^3*a₃*x*y^2 + 24*a₁^3*x^4*y - 32*a₁^3*x*y^3 + 6*a₁^2*a₂*a₃^2*x^2 + 24*a₁^2*a₂*a₃*x^2*y +
      24*a₁^2*a₂*x^2*y^2 - a₁^2*a₃^4 - 8*a₁^2*a₃^3*y + 18*a₁^2*a₃^2*x^3 - 24*a₁^2*a₃^2*y^2 +
      72*a₁^2*a₃*x^3*y - 32*a₁^2*a₃*y^3 + 72*a₁^2*x^3*y^2 - 16*a₁^2*y^4 + 4*a₁*a₂*a₃^3*x +
      24*a₁*a₂*a₃^2*x*y + 48*a₁*a₂*a₃*x*y^2 + 32*a₁*a₂*x*y^3 + 12*a₁*a₃^3*x^2 + 72*a₁*a₃^2*x^2*y +
      144*a₁*a₃*x^2*y^2 + 96*a₁*x^2*y^3 + a₂*a₃^4 + 8*a₂*a₃^3*y + 24*a₂*a₃^2*y^2 + 32*a₂*a₃*y^3 +
      16*a₂*y^4 + 3*a₃^4*x + 24*a₃^3*x*y + 72*a₃^2*x*y^2 + 96*a₃*x*y^3 + 48*x*y^4) * hdL
    + (-6*L^3*a₁^4*c*x^4 - 24*L^3*a₁^3*a₃*c*x^3 - 48*L^3*a₁^3*c*x^3*y - 36*L^3*a₁^2*a₃^2*c*x^2 -
      144*L^3*a₁^2*a₃*c*x^2*y - 144*L^3*a₁^2*c*x^2*y^2 - 24*L^3*a₁*a₃^3*c*x - 144*L^3*a₁*a₃^2*c*x*y -
      288*L^3*a₁*a₃*c*x*y^2 - 192*L^3*a₁*c*x*y^3 - 6*L^3*a₃^4*c - 48*L^3*a₃^3*c*y -
      144*L^3*a₃^2*c*y^2 - 192*L^3*a₃*c*y^3 - 96*L^3*c*y^4 - 11*L^2*a₁^5*c*x^4 - 44*L^2*a₁^4*a₃*c*x^3
      - 88*L^2*a₁^4*c*x^3*y - 66*L^2*a₁^3*a₃^2*c*x^2 - 264*L^2*a₁^3*a₃*c*x^2*y -
      264*L^2*a₁^3*c*x^2*y^2 - 44*L^2*a₁^2*a₃^3*c*x - 264*L^2*a₁^2*a₃^2*c*x*y -
      528*L^2*a₁^2*a₃*c*x*y^2 - 352*L^2*a₁^2*c*x*y^3 - 11*L^2*a₁*a₃^4*c - 88*L^2*a₁*a₃^3*c*y -
      264*L^2*a₁*a₃^2*c*y^2 - 352*L^2*a₁*a₃*c*y^3 - 176*L^2*a₁*c*y^4 - 6*L*a₁^6*c*x^4 -
      24*L*a₁^5*a₃*c*x^3 - 48*L*a₁^5*c*x^3*y + 2*L*a₁^4*a₂*c*x^4 - 36*L*a₁^4*a₃^2*c*x^2 -
      144*L*a₁^4*a₃*c*x^2*y + 6*L*a₁^4*c*x^5 - 144*L*a₁^4*c*x^2*y^2 + 8*L*a₁^3*a₂*a₃*c*x^3 +
      16*L*a₁^3*a₂*c*x^3*y - 24*L*a₁^3*a₃^3*c*x - 144*L*a₁^3*a₃^2*c*x*y + 24*L*a₁^3*a₃*c*x^4 -
      288*L*a₁^3*a₃*c*x*y^2 + 48*L*a₁^3*c*x^4*y - 192*L*a₁^3*c*x*y^3 + 12*L*a₁^2*a₂*a₃^2*c*x^2 +
      48*L*a₁^2*a₂*a₃*c*x^2*y + 48*L*a₁^2*a₂*c*x^2*y^2 - 6*L*a₁^2*a₃^4*c - 48*L*a₁^2*a₃^3*c*y +
      36*L*a₁^2*a₃^2*c*x^3 - 144*L*a₁^2*a₃^2*c*y^2 + 144*L*a₁^2*a₃*c*x^3*y - 192*L*a₁^2*a₃*c*y^3 +
      144*L*a₁^2*c*x^3*y^2 - 96*L*a₁^2*c*y^4 + 8*L*a₁*a₂*a₃^3*c*x + 48*L*a₁*a₂*a₃^2*c*x*y +
      96*L*a₁*a₂*a₃*c*x*y^2 + 64*L*a₁*a₂*c*x*y^3 + 24*L*a₁*a₃^3*c*x^2 + 144*L*a₁*a₃^2*c*x^2*y +
      288*L*a₁*a₃*c*x^2*y^2 + 192*L*a₁*c*x^2*y^3 + 2*L*a₂*a₃^4*c + 16*L*a₂*a₃^3*c*y +
      48*L*a₂*a₃^2*c*y^2 + 64*L*a₂*a₃*c*y^3 + 32*L*a₂*c*y^4 + 6*L*a₃^4*c*x + 48*L*a₃^3*c*x*y +
      144*L*a₃^2*c*x*y^2 + 192*L*a₃*c*x*y^3 + 96*L*c*x*y^4 - a₁^7*c*x^4 - 4*a₁^6*a₃*c*x^3 -
      8*a₁^6*c*x^3*y + a₁^5*a₂*c*x^4 - 6*a₁^5*a₃^2*c*x^2 - 24*a₁^5*a₃*c*x^2*y + 6*a₁^5*c*x^5 -
      24*a₁^5*c*x^2*y^2 + 4*a₁^4*a₂*a₃*c*x^3 + 8*a₁^4*a₂*c*x^3*y - 4*a₁^4*a₃^3*c*x -
      24*a₁^4*a₃^2*c*x*y + 27*a₁^4*a₃*c*x^4 - 48*a₁^4*a₃*c*x*y^2 + 54*a₁^4*c*x^4*y - 32*a₁^4*c*x*y^3
      + 6*a₁^3*a₂*a₃^2*c*x^2 + 24*a₁^3*a₂*a₃*c*x^2*y + 24*a₁^3*a₂*c*x^2*y^2 - a₁^3*a₃^4*c -
      8*a₁^3*a₃^3*c*y + 48*a₁^3*a₃^2*c*x^3 - 24*a₁^3*a₃^2*c*y^2 + 192*a₁^3*a₃*c*x^3*y -
      32*a₁^3*a₃*c*y^3 + 192*a₁^3*c*x^3*y^2 - 16*a₁^3*c*y^4 + 4*a₁^2*a₂*a₃^3*c*x +
      24*a₁^2*a₂*a₃^2*c*x*y + 48*a₁^2*a₂*a₃*c*x*y^2 + 32*a₁^2*a₂*c*x*y^3 + 42*a₁^2*a₃^3*c*x^2 +
      252*a₁^2*a₃^2*c*x^2*y + 504*a₁^2*a₃*c*x^2*y^2 + 336*a₁^2*c*x^2*y^3 + a₁*a₂*a₃^4*c +
      8*a₁*a₂*a₃^3*c*y + 24*a₁*a₂*a₃^2*c*y^2 + 32*a₁*a₂*a₃*c*y^3 + 16*a₁*a₂*c*y^4 + 18*a₁*a₃^4*c*x +
      144*a₁*a₃^3*c*x*y + 432*a₁*a₃^2*c*x*y^2 + 576*a₁*a₃*c*x*y^3 + 288*a₁*c*x*y^4 + 3*a₃^5*c +
      30*a₃^4*c*y + 120*a₃^3*c*y^2 + 240*a₃^2*c*y^3 + 240*a₃*c*y^4 + 96*c*y^5) * hL
    + (0) * h

end WeierstrassCurve.S1Additivity
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

namespace Derivation
p2m_export "Derivation" "map_aeval leibniz_div map_algebraMap leibniz_pow leibniz ext mk map_natCast map_intCast"
p2m_open "Derivation"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve WeierstrassCurve.Affine"

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]
  (W : WeierstrassCurve K) (D : Derivation K L L)

private theorem map_baseChange_a (D : Derivation K L L) (W : WeierstrassCurve K) :
    D (W.baseChange L).a₁ = 0 ∧ D (W.baseChange L).a₂ = 0 ∧ D (W.baseChange L).a₃ = 0 ∧
      D (W.baseChange L).a₄ = 0 ∧ D (W.baseChange L).a₆ = 0 :=
  ⟨D.map_algebraMap _, D.map_algebraMap _, D.map_algebraMap _, D.map_algebraMap _, D.map_algebraMap _⟩

theorem apply_addX_of_X_ne {x₁ y₁ x₂ y₂ c₁ c₂ : L}
    (h₁ : (W.baseChange L).toAffine.Equation x₁ y₁) (h₂ : (W.baseChange L).toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂)
    (hDx₁ : D x₁ = c₁ * (2 * y₁ + (W.baseChange L).a₁ * x₁ + (W.baseChange L).a₃))
    (hDy₁ : D y₁ = c₁ * (3 * x₁ ^ 2 + 2 * (W.baseChange L).a₂ * x₁ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₁))
    (hDx₂ : D x₂ = c₂ * (2 * y₂ + (W.baseChange L).a₁ * x₂ + (W.baseChange L).a₃))
    (hDy₂ : D y₂ = c₂ * (3 * x₂ ^ 2 + 2 * (W.baseChange L).a₂ * x₂ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₂)) :
    D ((W.baseChange L).toAffine.addX x₁ x₂ ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂))
      = (c₁ + c₂) * (2 * (W.baseChange L).toAffine.addY x₁ x₂ y₁
            ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂)
          + (W.baseChange L).a₁ * (W.baseChange L).toAffine.addX x₁ x₂
            ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂)
          + (W.baseChange L).a₃) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := map_baseChange_a D W
  set W' := W.baseChange L with hW'
  set ℓ := W'.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  have hu : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hL : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓ, slope_of_X_ne hx, div_mul_cancel₀ _ hu]
  have e := congrArg D hL
  simp only [Derivation.leibniz, map_sub, smul_eq_mul] at e
  have hdL : D ℓ * (x₁ - x₂)
      = (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁)
          - c₂ * (3 * x₂ ^ 2 + 2 * W'.a₂ * x₂ + W'.a₄ - W'.a₁ * y₂))
        - ℓ * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃) - c₂ * (2 * y₂ + W'.a₁ * x₂ + W'.a₃)) := by
    rw [hDx₁, hDx₂, hDy₁, hDy₂] at e
    linear_combination e
  have hx₃ : W'.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂ := rfl
  have hy₃ : W'.toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * (W'.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₂ ℓ - W'.a₃ := rfl
  have eDx : D (W'.toAffine.addX x₁ x₂ ℓ) = (2 * ℓ + W'.a₁) * D ℓ - D x₁ - D x₂ := by
    rw [hx₃]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂]
    ring
  have h₁' := (W'.toAffine.equation_iff x₁ y₁).mp h₁
  have h₂' := (W'.toAffine.equation_iff x₂ y₂).mp h₂
  have cert := WeierstrassCurve.S1Additivity.chord_dx W'.a₁ W'.a₂ W'.a₃ W'.a₄ W'.a₆ x₁ y₁ x₂ y₂ c₁ c₂
    ℓ (D ℓ) (W'.toAffine.addX x₁ x₂ ℓ) (W'.toAffine.addY x₁ x₂ y₁ ℓ) h₁' h₂' hL hdL hx₃ hy₃
  have key := (mul_eq_zero.mp cert).resolve_left (pow_ne_zero _ hu)
  rw [eDx, hDx₁, hDx₂]
  linear_combination key

theorem apply_addY_of_X_ne {x₁ y₁ x₂ y₂ c₁ c₂ : L}
    (h₁ : (W.baseChange L).toAffine.Equation x₁ y₁) (h₂ : (W.baseChange L).toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂)
    (hDx₁ : D x₁ = c₁ * (2 * y₁ + (W.baseChange L).a₁ * x₁ + (W.baseChange L).a₃))
    (hDy₁ : D y₁ = c₁ * (3 * x₁ ^ 2 + 2 * (W.baseChange L).a₂ * x₁ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₁))
    (hDx₂ : D x₂ = c₂ * (2 * y₂ + (W.baseChange L).a₁ * x₂ + (W.baseChange L).a₃))
    (hDy₂ : D y₂ = c₂ * (3 * x₂ ^ 2 + 2 * (W.baseChange L).a₂ * x₂ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₂)) :
    D ((W.baseChange L).toAffine.addY x₁ x₂ y₁ ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂))
      = (c₁ + c₂) * (3 * (W.baseChange L).toAffine.addX x₁ x₂
              ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂) ^ 2
          + 2 * (W.baseChange L).a₂ * (W.baseChange L).toAffine.addX x₁ x₂
              ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂)
          + (W.baseChange L).a₄
          - (W.baseChange L).a₁ * (W.baseChange L).toAffine.addY x₁ x₂ y₁
              ((W.baseChange L).toAffine.slope x₁ x₂ y₁ y₂)) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := map_baseChange_a D W
  set W' := W.baseChange L with hW'
  set ℓ := W'.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  have hu : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hL : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓ, slope_of_X_ne hx, div_mul_cancel₀ _ hu]
  have e := congrArg D hL
  simp only [Derivation.leibniz, map_sub, smul_eq_mul] at e
  have hdL : D ℓ * (x₁ - x₂)
      = (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁)
          - c₂ * (3 * x₂ ^ 2 + 2 * W'.a₂ * x₂ + W'.a₄ - W'.a₁ * y₂))
        - ℓ * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃) - c₂ * (2 * y₂ + W'.a₁ * x₂ + W'.a₃)) := by
    rw [hDx₁, hDx₂, hDy₁, hDy₂] at e
    linear_combination e
  have hx₃ : W'.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂ := rfl
  have hy₃ : W'.toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * (W'.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₂ ℓ - W'.a₃ := rfl
  have eDx : D (W'.toAffine.addX x₁ x₂ ℓ) = (2 * ℓ + W'.a₁) * D ℓ - D x₁ - D x₂ := by
    rw [hx₃]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂]
    ring
  have eDy : D (W'.toAffine.addY x₁ x₂ y₁ ℓ)
      = -(D ℓ * (W'.toAffine.addX x₁ x₂ ℓ - x₁) + ℓ * (D (W'.toAffine.addX x₁ x₂ ℓ) - D x₁) + D y₁)
        - W'.a₁ * D (W'.toAffine.addX x₁ x₂ ℓ) := by
    conv_lhs => rw [hy₃]
    simp only [Derivation.leibniz, map_sub, map_add, map_neg, smul_eq_mul, ha₁, ha₃]
    ring
  have h₁' := (W'.toAffine.equation_iff x₁ y₁).mp h₁
  have h₂' := (W'.toAffine.equation_iff x₂ y₂).mp h₂
  have cert := WeierstrassCurve.S1Additivity.chord_dy W'.a₁ W'.a₂ W'.a₃ W'.a₄ W'.a₆ x₁ y₁ x₂ y₂ c₁ c₂
    ℓ (D ℓ) (W'.toAffine.addX x₁ x₂ ℓ) (W'.toAffine.addY x₁ x₂ y₁ ℓ) h₁' h₂' hL hdL hx₃ hy₃
  have key := (mul_eq_zero.mp cert).resolve_left (pow_ne_zero _ hu)
  rw [eDy, eDx, hDx₁, hDx₂, hDy₁]
  linear_combination key

theorem apply_addX_self {x₁ y₁ c₁ : L}
    (h₁ : (W.baseChange L).toAffine.Equation x₁ y₁) (hy : y₁ ≠ (W.baseChange L).toAffine.negY x₁ y₁)
    (hDx₁ : D x₁ = c₁ * (2 * y₁ + (W.baseChange L).a₁ * x₁ + (W.baseChange L).a₃))
    (hDy₁ : D y₁ = c₁ * (3 * x₁ ^ 2 + 2 * (W.baseChange L).a₂ * x₁ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₁)) :
    D ((W.baseChange L).toAffine.addX x₁ x₁ ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁))
      = (c₁ + c₁) * (2 * (W.baseChange L).toAffine.addY x₁ x₁ y₁
            ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁)
          + (W.baseChange L).a₁ * (W.baseChange L).toAffine.addX x₁ x₁
            ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁)
          + (W.baseChange L).a₃) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := map_baseChange_a D W
  set W' := W.baseChange L with hW'
  set ℓ := W'.toAffine.slope x₁ x₁ y₁ y₁ with hℓ
  have hden : y₁ - W'.toAffine.negY x₁ y₁ = 2 * y₁ + W'.a₁ * x₁ + W'.a₃ := by
    rw [negY]; ring
  have hu : 2 * y₁ + W'.a₁ * x₁ + W'.a₃ ≠ 0 := by rw [← hden]; exact sub_ne_zero.mpr hy
  have hL : ℓ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃) = 3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁ := by
    rw [hℓ, slope_of_Y_ne rfl hy, hden, div_mul_cancel₀ _ hu]
  have h2 : D (2 : L) = 0 := by
    rw [show (2 : L) = algebraMap K L 2 from (map_ofNat (algebraMap K L) 2).symm]; exact D.map_algebraMap _
  have h3 : D (3 : L) = 0 := by
    rw [show (3 : L) = algebraMap K L 3 from (map_ofNat (algebraMap K L) 3).symm]; exact D.map_algebraMap _
  have e := congrArg D hL
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂, ha₃,
    ha₄, h2, h3] at e
  have hdL : D ℓ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃)
      = (6 * x₁ + 2 * W'.a₂) * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃))
          - W'.a₁ * (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁))
        - ℓ * (2 * (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁))
          + W'.a₁ * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃))) := by
    rw [hDx₁, hDy₁] at e
    linear_combination e
  have hx₃ : W'.toAffine.addX x₁ x₁ ℓ = ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₁ := rfl
  have hy₃ : W'.toAffine.addY x₁ x₁ y₁ ℓ
      = -(ℓ * (W'.toAffine.addX x₁ x₁ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₁ ℓ - W'.a₃ := rfl
  have eDx : D (W'.toAffine.addX x₁ x₁ ℓ) = (2 * ℓ + W'.a₁) * D ℓ - D x₁ - D x₁ := by
    rw [hx₃]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂]
    ring
  have h₁' := (W'.toAffine.equation_iff x₁ y₁).mp h₁
  have cert := WeierstrassCurve.S1Additivity.tangent_dx W'.a₁ W'.a₂ W'.a₃ W'.a₄ W'.a₆ x₁ y₁ c₁
    ℓ (D ℓ) (W'.toAffine.addX x₁ x₁ ℓ) (W'.toAffine.addY x₁ x₁ y₁ ℓ) h₁' hL hdL hx₃ hy₃
  have key := (mul_eq_zero.mp cert).resolve_left (pow_ne_zero _ hu)
  rw [eDx, hDx₁]
  linear_combination key

theorem apply_addY_self {x₁ y₁ c₁ : L}
    (h₁ : (W.baseChange L).toAffine.Equation x₁ y₁) (hy : y₁ ≠ (W.baseChange L).toAffine.negY x₁ y₁)
    (hDx₁ : D x₁ = c₁ * (2 * y₁ + (W.baseChange L).a₁ * x₁ + (W.baseChange L).a₃))
    (hDy₁ : D y₁ = c₁ * (3 * x₁ ^ 2 + 2 * (W.baseChange L).a₂ * x₁ + (W.baseChange L).a₄
      - (W.baseChange L).a₁ * y₁)) :
    D ((W.baseChange L).toAffine.addY x₁ x₁ y₁ ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁))
      = (c₁ + c₁) * (3 * (W.baseChange L).toAffine.addX x₁ x₁
              ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁) ^ 2
          + 2 * (W.baseChange L).a₂ * (W.baseChange L).toAffine.addX x₁ x₁
              ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁)
          + (W.baseChange L).a₄
          - (W.baseChange L).a₁ * (W.baseChange L).toAffine.addY x₁ x₁ y₁
              ((W.baseChange L).toAffine.slope x₁ x₁ y₁ y₁)) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := map_baseChange_a D W
  set W' := W.baseChange L with hW'
  set ℓ := W'.toAffine.slope x₁ x₁ y₁ y₁ with hℓ
  have hden : y₁ - W'.toAffine.negY x₁ y₁ = 2 * y₁ + W'.a₁ * x₁ + W'.a₃ := by
    rw [negY]; ring
  have hu : 2 * y₁ + W'.a₁ * x₁ + W'.a₃ ≠ 0 := by rw [← hden]; exact sub_ne_zero.mpr hy
  have hL : ℓ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃) = 3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁ := by
    rw [hℓ, slope_of_Y_ne rfl hy, hden, div_mul_cancel₀ _ hu]
  have h2 : D (2 : L) = 0 := by
    rw [show (2 : L) = algebraMap K L 2 from (map_ofNat (algebraMap K L) 2).symm]; exact D.map_algebraMap _
  have h3 : D (3 : L) = 0 := by
    rw [show (3 : L) = algebraMap K L 3 from (map_ofNat (algebraMap K L) 3).symm]; exact D.map_algebraMap _
  have e := congrArg D hL
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂, ha₃,
    ha₄, h2, h3] at e
  have hdL : D ℓ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃)
      = (6 * x₁ + 2 * W'.a₂) * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃))
          - W'.a₁ * (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁))
        - ℓ * (2 * (c₁ * (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁))
          + W'.a₁ * (c₁ * (2 * y₁ + W'.a₁ * x₁ + W'.a₃))) := by
    rw [hDx₁, hDy₁] at e
    linear_combination e
  have hx₃ : W'.toAffine.addX x₁ x₁ ℓ = ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₁ := rfl
  have hy₃ : W'.toAffine.addY x₁ x₁ y₁ ℓ
      = -(ℓ * (W'.toAffine.addX x₁ x₁ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₁ ℓ - W'.a₃ := rfl
  have eDx : D (W'.toAffine.addX x₁ x₁ ℓ) = (2 * ℓ + W'.a₁) * D ℓ - D x₁ - D x₁ := by
    rw [hx₃]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, ha₁, ha₂]
    ring
  have eDy : D (W'.toAffine.addY x₁ x₁ y₁ ℓ)
      = -(D ℓ * (W'.toAffine.addX x₁ x₁ ℓ - x₁) + ℓ * (D (W'.toAffine.addX x₁ x₁ ℓ) - D x₁) + D y₁)
        - W'.a₁ * D (W'.toAffine.addX x₁ x₁ ℓ) := by
    conv_lhs => rw [hy₃]
    simp only [Derivation.leibniz, map_sub, map_add, map_neg, smul_eq_mul, ha₁, ha₃]
    ring
  have h₁' := (W'.toAffine.equation_iff x₁ y₁).mp h₁
  have cert := WeierstrassCurve.S1Additivity.tangent_dy W'.a₁ W'.a₂ W'.a₃ W'.a₄ W'.a₆ x₁ y₁ c₁
    ℓ (D ℓ) (W'.toAffine.addX x₁ x₁ ℓ) (W'.toAffine.addY x₁ x₁ y₁ ℓ) h₁' hL hdL hx₃ hy₃
  have key := (mul_eq_zero.mp cert).resolve_left (pow_ne_zero _ hu)
  rw [eDy, eDx, hDx₁, hDy₁]
  linear_combination key

end Derivation
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

set_option autoImplicit false

p2m_open "Polynomial"
p2m_open_scoped "Polynomial.Bivariate"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
p2m_open "WeierstrassCurve"

section pointLemmas

variable {F : Type*} [Field F] (V : WeierstrassCurve F)

theorem eq_or_eq_negY_of_equation' {x y₁ y₂ : F}
    (h₁ : V.toAffine.Equation x y₁) (h₂ : V.toAffine.Equation x y₂) :
    y₂ = y₁ ∨ y₂ = V.toAffine.negY x y₁ := by
  rw [Affine.equation_iff] at h₁ h₂
  have : (y₂ - y₁) * (y₂ - (-y₁ - V.a₁ * x - V.a₃)) = 0 := by linear_combination h₂ - h₁
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

theorem some_eq_or_eq_neg_of_X_eq {x y₁ y₂ : F}
    (h₁ : V.toAffine.Nonsingular x y₁) (h₂ : V.toAffine.Nonsingular x y₂) :
    Affine.Point.some x y₂ h₂ = Affine.Point.some x y₁ h₁ ∨
      Affine.Point.some x y₂ h₂ = -Affine.Point.some x y₁ h₁ := by
  rcases eq_or_eq_negY_of_equation' V h₁.1 h₂.1 with rfl | rfl
  · exact Or.inl rfl
  · right; rw [Affine.Point.neg_some]

end pointLemmas
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

namespace InvariantDerivation

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

noncomputable scoped instance instDecEqL : DecidableEq (L W) := Classical.decEq _

theorem EL_a₁ : (EL W).a₁ = algebraMap K (L W) W.a₁ := rfl
theorem EL_a₂ : (EL W).a₂ = algebraMap K (L W) W.a₂ := rfl
theorem EL_a₃ : (EL W).a₃ = algebraMap K (L W) W.a₃ := rfl
theorem EL_a₄ : (EL W).a₄ = algebraMap K (L W) W.a₄ := rfl

noncomputable def FY (u v : L W) : L W := 2 * v + (EL W).a₁ * u + (EL W).a₃

noncomputable def GX (u v : L W) : L W :=
  3 * u ^ 2 + 2 * (EL W).a₂ * u + (EL W).a₄ - (EL W).a₁ * v

theorem D_x₀' : D W (x₀ W) = 1 * FY W (x₀ W) (y₀ W) := by
  rw [D_x₀, fY, FY, EL_a₁, EL_a₃, one_mul]

theorem D_y₀' : D W (y₀ W) = 1 * GX W (x₀ W) (y₀ W) := by
  rw [D_y₀, negfX, GX, EL_a₁, EL_a₂, EL_a₄, one_mul]

theorem negY_taut :
    (EL W).toAffine.negY (x₀ W) (y₀ W) = -y₀ W - (EL W).a₁ * x₀ W - (EL W).a₃ := rfl

theorem y₀_ne_negY (h2 : (2 : K) ≠ 0) : y₀ W ≠ (EL W).toAffine.negY (x₀ W) (y₀ W) := by
  intro h
  apply fY_ne_zero W h2
  rw [fY, ← EL_a₁, ← EL_a₃]
  rw [negY_taut] at h
  linear_combination h

theorem multiplier (h2 : (2 : K) ≠ 0) (N : ℕ)
    (hN : ∀ k, 1 ≤ k → k ≤ N → k • P₀ W h2 ≠ 0) :
    ∀ m, 1 ≤ m → m ≤ N → ∃ (Xm Ym : L W) (h : (EL W).toAffine.Nonsingular Xm Ym),
      m • P₀ W h2 = .some Xm Ym h ∧ D W Xm = (m : L W) * FY W Xm Ym ∧
        D W Ym = (m : L W) * GX W Xm Ym := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    exact ⟨x₀ W, y₀ W, nonsingular_taut W h2, one_nsmul _, by rw [Nat.cast_one]; exact D_x₀' W,
      by rw [Nat.cast_one]; exact D_y₀' W⟩
  | succ m hm ih =>
    intro hmN
    obtain ⟨Xm, Ym, h, hmP, hDX, hDY⟩ := ih (Nat.le_of_succ_le hmN)
    have h₀ := nonsingular_taut W h2
    have hsum : (m + 1) • P₀ W h2 = Affine.Point.some Xm Ym h + Affine.Point.some (x₀ W) (y₀ W) h₀ := by
      rw [succ_nsmul, hmP]; rfl
    by_cases hx : Xm = x₀ W
    · subst hx
      rcases some_eq_or_eq_neg_of_X_eq (EL W) h₀ h with heq | heq
      ·
        have hm1 : m = 1 := by
          by_contra hm1
          apply hN (m - 1) (by omega) (by omega)
          have e : (m - 1) • P₀ W h2 + P₀ W h2 = m • P₀ W h2 := by
            rw [← succ_nsmul]; congr 1; omega
          rw [hmP, heq] at e
          change (m - 1) • P₀ W h2 + P₀ W h2 = P₀ W h2 at e
          exact add_right_cancel (e.trans (zero_add _).symm)
        subst hm1
        have hYm : Ym = y₀ W := by injection heq
        subst hYm
        have hy := y₀_ne_negY W h2
        rw [Affine.Point.add_self_of_Y_ne (h₁ := h) hy] at hsum
        refine ⟨_, _, _, hsum, ?_, ?_⟩
        · rw [Derivation.apply_addX_self W (D W) h.1 hy hDX hDY]
          push_cast; simp only [FY]; ring
        · rw [Derivation.apply_addY_self W (D W) h.1 hy hDX hDY]
          push_cast; simp only [GX]; ring
      ·
        exfalso
        apply hN (m + 1) (by omega) hmN
        rw [hsum, heq, neg_add_cancel]
    ·
      rw [Affine.Point.add_of_X_ne hx] at hsum
      refine ⟨_, _, _, hsum, ?_, ?_⟩
      · rw [Derivation.apply_addX_of_X_ne W (D W) h.1 h₀.1 hx hDX hDY (D_x₀' W) (D_y₀' W)]
        push_cast; simp only [FY]
      · rw [Derivation.apply_addY_of_X_ne W (D W) h.1 h₀.1 hx hDX hDY (D_x₀' W) (D_y₀' W)]
        push_cast; simp only [GX]

end InvariantDerivation
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

set_option autoImplicit false

p2m_open "Polynomial"
p2m_open_scoped "Polynomial.Bivariate"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
p2m_open "WeierstrassCurve"

namespace InvariantDerivation

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

theorem eval_map_x₀ (q : K[X]) : (q.map (algebraMap K (L W))).eval (x₀ W) = aeval (x₀ W) q := by
  rw [eval_map, ← aeval_def]

theorem EL_ΨSq (n : ℤ) : (EL W).ΨSq n = (W.ΨSq n).map (algebraMap K (L W)) := by
  rw [EL, baseChange, map_ΨSq]

theorem EL_Φ (n : ℤ) : (EL W).Φ n = (W.Φ n).map (algebraMap K (L W)) := by
  rw [EL, baseChange, map_Φ]

theorem fY_eq_FY : fY W = FY W (x₀ W) (y₀ W) := by
  rw [fY, FY, EL_a₁, EL_a₃]

theorem FY_sq_eq {u v : L W} (h : (EL W).toAffine.Equation u v) :
    FY W u v ^ 2 = (EL W).Ψ₂Sq.eval u := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [FY, Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination 4 * h

theorem Ψ₂Sq_eval_div (φ s : L W) (hs : s ≠ 0) :
    (EL W).Ψ₂Sq.eval (φ / s) * s ^ 3 =
      4 * φ ^ 3 + algebraMap K (L W) W.b₂ * φ ^ 2 * s
        + 2 * algebraMap K (L W) W.b₄ * φ * s ^ 2 + algebraMap K (L W) W.b₆ * s ^ 3 := by
  simp only [EL, baseChange, Ψ₂Sq, map_b₂, map_b₄, map_b₆, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    eval_ofNat, map_mul, map_ofNat]
  field_simp
  all_goals ring

variable [CharZero K]

theorem charZero_L : CharZero (L W) :=
  charZero_of_injective_algebraMap (algebraMap K (L W)).injective

theorem ΨSq_aeval_ne_zero (n : ℤ) (hn : n ≠ 0) : aeval (x₀ W) (W.ΨSq n) ≠ 0 := by
  intro h
  have h0 : W.ΨSq n = 0 := aeval_x₀_injective W (by rw [h, map_zero])
  have hl := W.leadingCoeff_ΨSq (n := n) (by exact_mod_cast hn)
  rw [h0, leadingCoeff_zero] at hl
  exact (pow_ne_zero 2 (Int.cast_ne_zero.mpr hn : (n : K) ≠ 0)) hl.symm

theorem psi_evalEval_ne_zero (n : ℤ) (hn : n ≠ 0) :
    ((EL W).ψ n).evalEval (x₀ W) (y₀ W) ≠ 0 := by
  intro h
  have := WeierstrassCurve.Affine.evalEval_psi_sq (EL W) (equation_taut W) n
  rw [h, EL_ΨSq, eval_map_x₀] at this
  exact ΨSq_aeval_ne_zero W n hn (by simpa using this.symm)

theorem nsmul_P₀_ne_zero (k : ℕ) (hk : 1 ≤ k) : k • P₀ W two_ne_zero ≠ 0 := by
  intro h
  have h' : (k : ℤ) • P₀ W two_ne_zero = 0 := by rw [natCast_zsmul]; exact h
  change (k : ℤ) • Affine.Point.some (x₀ W) (y₀ W) (nonsingular_taut W two_ne_zero) = 0 at h'
  rw [WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff] at h'
  exact psi_evalEval_ne_zero W k (by exact_mod_cast (by omega : k ≠ 0)) h'

theorem multiplier_all (m : ℕ) (hm : 1 ≤ m) :
    ∃ (Xm Ym : L W) (h : (EL W).toAffine.Nonsingular Xm Ym),
      m • P₀ W two_ne_zero = .some Xm Ym h ∧ D W Xm = (m : L W) * FY W Xm Ym ∧
        D W Ym = (m : L W) * GX W Xm Ym :=
  multiplier W two_ne_zero m (fun k hk _ => nsmul_P₀_ne_zero W k hk) m hm le_rfl

omit [CharZero K] in

theorem D_aeval_div (P Q : K[X]) (hQ : aeval (x₀ W) Q ≠ 0) :
    D W (aeval (x₀ W) P / aeval (x₀ W) Q) * aeval (x₀ W) Q ^ 2 =
      aeval (x₀ W) (derivative P * Q - P * derivative Q) * fY W := by
  rw [Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval, D_x₀]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp
  all_goals ring

theorem Ψ₂Sq_mul_wronskian_sq_of_charZero (n : ℤ) (hn : 1 ≤ n) :
    W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
      C ((n : K) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
        + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) := by
  classical

  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (n : ℤ) = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hm : 1 ≤ m := by exact_mod_cast hn
  set s := aeval (x₀ W) (W.ΨSq m) with hs_def
  set φ := aeval (x₀ W) (W.Φ m) with hφ_def
  have hs : s ≠ 0 := ΨSq_aeval_ne_zero W m (by exact_mod_cast (by omega : m ≠ 0))

  obtain ⟨Xm, Ym, h, hmP, hDX, -⟩ := multiplier_all W m hm
  obtain ⟨y', h', hzs⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (EL W)
    (nonsingular_taut W two_ne_zero) (n := (m : ℤ))
    (psi_evalEval_ne_zero W m (by exact_mod_cast (by omega : m ≠ 0)))
  rw [natCast_zsmul] at hzs
  change m • P₀ W two_ne_zero = _ at hzs
  rw [hmP] at hzs
  have hX : Xm = φ / s := by
    injection hzs with hX _
    rw [hX, EL_Φ, EL_ΨSq, eval_map_x₀, eval_map_x₀]

  have key : aeval (x₀ W) (derivative (W.Φ m) * W.ΨSq m - W.Φ m * derivative (W.ΨSq m)) * fY W
      = (m : L W) * FY W Xm Ym * s ^ 2 := by
    rw [← D_aeval_div W _ _ hs, ← hX, hDX]

  have hsq1 : fY W ^ 2 = aeval (x₀ W) W.Ψ₂Sq := by
    rw [fY_eq_FY, FY_sq_eq W (equation_taut W), EL, baseChange, map_Ψ₂Sq, eval_map_x₀]
  have hsq2 : FY W Xm Ym ^ 2 * s ^ 3 = 4 * φ ^ 3
      + algebraMap K (L W) W.b₂ * φ ^ 2 * s + 2 * algebraMap K (L W) W.b₄ * φ * s ^ 2
      + algebraMap K (L W) W.b₆ * s ^ 3 := by
    rw [FY_sq_eq W h.1, hX, Ψ₂Sq_eval_div W φ s hs]
  have k2 : aeval (x₀ W) (derivative (W.Φ m) * W.ΨSq m - W.Φ m * derivative (W.ΨSq m)) ^ 2
      * aeval (x₀ W) W.Ψ₂Sq = (m : L W) ^ 2 * FY W Xm Ym ^ 2 * s ^ 4 := by
    have := congrArg (· ^ 2) key
    simp only [mul_pow] at this
    rw [hsq1] at this
    linear_combination this

  apply aeval_x₀_injective W
  simp only [map_mul, map_pow, map_add, map_sub, aeval_C, map_intCast, Int.cast_natCast, map_natCast,
    map_ofNat]
  simp only [map_sub, map_mul] at k2
  rw [← hs_def, ← hφ_def] at k2 ⊢
  linear_combination k2 + (m : L W) ^ 2 * s * hsq2

end InvariantDerivation
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

noncomputable section

open MvPolynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
namespace Universal
p2m_open "WeierstrassCurve"

abbrev R₀ : Type := MvPolynomial (Fin 5) ℤ

def 𝓦 : WeierstrassCurve R₀ := ⟨X 0, X 1, X 2, X 3, X 4⟩

def univHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) : R₀ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

@[scoped simp] theorem univHom_X0 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 0) = W.a₁ := by simp [univHom]
@[scoped simp] theorem univHom_X1 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 1) = W.a₂ := by simp [univHom]
@[scoped simp] theorem univHom_X2 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 2) = W.a₃ := by simp [univHom]
@[scoped simp] theorem univHom_X3 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 3) = W.a₄ := by simp [univHom]
@[scoped simp] theorem univHom_X4 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : univHom W (X 4) = W.a₆ := by simp [univHom]

theorem map_univHom {R : Type*} [CommRing R] (W : WeierstrassCurve R) : 𝓦.map (univHom W) = W := by
  ext
  · show univHom W (X 0) = W.a₁; simp
  · show univHom W (X 1) = W.a₂; simp
  · show univHom W (X 2) = W.a₃; simp
  · show univHom W (X 3) = W.a₄; simp
  · show univHom W (X 4) = W.a₆; simp

abbrev Rp (p : ℕ) : Type := MvPolynomial (Fin 5) (ZMod p)

abbrev Fp (p : ℕ) [Fact p.Prime] : Type := FractionRing (Rp p)

def 𝓦p (p : ℕ) : WeierstrassCurve (Rp p) := ⟨X 0, X 1, X 2, X 3, X 4⟩

theorem 𝓦p_eq_map (p : ℕ) : 𝓦p p = 𝓦.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · show (X 0 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 0); rw [MvPolynomial.map_X]
  · show (X 1 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 1); rw [MvPolynomial.map_X]
  · show (X 2 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 2); rw [MvPolynomial.map_X]
  · show (X 3 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 3); rw [MvPolynomial.map_X]
  · show (X 4 : Rp p) = MvPolynomial.map (Int.castRingHom (ZMod p)) (X 4); rw [MvPolynomial.map_X]

def univHomP {R : Type*} [CommRing R] (p : ℕ) [CharP R p] (W : WeierstrassCurve R) : Rp p →+* R :=
  MvPolynomial.eval₂Hom (ZMod.castHom (dvd_refl p) R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_univHomP {R : Type*} [CommRing R] (p : ℕ) [CharP R p] (W : WeierstrassCurve R) :
    (𝓦p p).map (univHomP p W) = W := by
  ext
  · show univHomP p W (X 0) = W.a₁; simp [univHomP]
  · show univHomP p W (X 1) = W.a₂; simp [univHomP]
  · show univHomP p W (X 2) = W.a₃; simp [univHomP]
  · show univHomP p W (X 3) = W.a₄; simp [univHomP]
  · show univHomP p W (X 4) = W.a₆; simp [univHomP]

def ev1728 (p : ℕ) : Rp p →+* ZMod p := MvPolynomial.eval ![0, 0, 0, 1, 0]

theorem map_ev1728 (p : ℕ) : (𝓦p p).map (ev1728 p) = WeierstrassCurve.ofJ1728 (ZMod p) := by
  ext
  · show ev1728 p (X 0) = 0; simp [ev1728]
  · show ev1728 p (X 1) = 0; simp [ev1728]
  · show ev1728 p (X 2) = 0; simp [ev1728]
  · show ev1728 p (X 3) = 1; simp [ev1728]
  · show ev1728 p (X 4) = 0; simp [ev1728]

theorem two_ne_zero_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem Δ_𝓦p_ne_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (𝓦p p).Δ ≠ 0 := by
  intro h
  have := congrArg (ev1728 p) h
  rw [← WeierstrassCurve.map_Δ, map_ev1728, WeierstrassCurve.ofJ1728_Δ, map_zero, neg_eq_zero,
    show (64 : ZMod p) = 2 ^ 6 by norm_num] at this
  exact pow_ne_zero 6 (two_ne_zero_zmod p hp2) this

scoped instance charP_Fp (p : ℕ) [Fact p.Prime] : CharP (Fp p) p :=
  charP_of_injective_algebraMap (IsFractionRing.injective (Rp p) (Fp p)) p

theorem isElliptic_𝓦p_Fp (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((𝓦p p).map (algebraMap (Rp p) (Fp p))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
  exact fun h => Δ_𝓦p_ne_zero p hp2 ((IsFractionRing.injective (Rp p) (Fp p)) (by rw [h, map_zero]))

theorem two_ne_zero_Fp (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : Fp p) ≠ 0 := by
  have : ((2 : ℕ) : Fp p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (Fp p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simpa using this

theorem four_ne_zero_Rp (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (4 : Rp p) ≠ 0 := by
  have h2 : ((2 : ℕ) : Rp p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (Rp p) p]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have : (4 : Rp p) = ((2 : ℕ) : Rp p) ^ 2 := by norm_num
  rw [this]; exact pow_ne_zero 2 h2

end WeierstrassCurve.Universal
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"

noncomputable section

p2m_open "Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
p2m_open "WeierstrassCurve"

variable {R : Type*} [CommRing R]

def wrLHS (W : WeierstrassCurve R) (n : ℤ) : R[X] :=
  W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2

def wrRHS (W : WeierstrassCurve R) (n : ℤ) : R[X] :=
  C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
    + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3))

def UIdentity (W : WeierstrassCurve R) (n : ℤ) : Prop :=
  W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
    C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
      + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3))

theorem uIdentity_iff (W : WeierstrassCurve R) (n : ℤ) : UIdentity W n ↔ wrLHS W n = wrRHS W n := Iff.rfl

variable {S : Type*} [CommRing S]

theorem wrLHS_map (W : WeierstrassCurve R) (f : R →+* S) (n : ℤ) :
    (wrLHS W n).map f = wrLHS (W.map f) n := by
  simp only [wrLHS, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, derivative_map,
    map_Ψ₂Sq, map_Φ, map_ΨSq]

theorem wrRHS_map (W : WeierstrassCurve R) (f : R →+* S) (n : ℤ) :
    (wrRHS W n).map f = wrRHS (W.map f) n := by
  simp only [wrRHS, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, map_Φ,
    map_ΨSq, map_b₂, map_b₄, map_b₆]
  rw [map_pow f, map_intCast, map_ofNat f 4, map_mul f, map_ofNat f 2]

theorem UIdentity.map {W : WeierstrassCurve R} {n : ℤ} (h : UIdentity W n) (f : R →+* S) :
    UIdentity (W.map f) n := by
  rw [uIdentity_iff] at h ⊢
  rw [← wrLHS_map, ← wrRHS_map, h]

theorem UIdentity.of_map {W : WeierstrassCurve R} {n : ℤ} (f : R →+* S) (hf : Function.Injective f)
    (h : UIdentity (W.map f) n) : UIdentity W n := by
  rw [uIdentity_iff] at h ⊢
  rw [← wrLHS_map, ← wrRHS_map] at h
  exact Polynomial.map_injective f hf h

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"

noncomputable section

p2m_open "Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine ΨSq_zero Affine.Equation a₃ leadingCoeff_ΨSq a₁ map map_b₂ map_Φ b₂ Φ_zero mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' ΨSq_neg Affine.degree_polynomial ofJ1728_Δ reduction Affine.map_polynomial ofJ1728 map_ΨSq ΨSq toAffine Affine.Point map_b₆ map_injective map_Δ Affine.monic_polynomial b₆ Δ Affine.Point.add_of_X_ne Affine.equation_iff Φ_neg Affine.polynomial Affine.Point.neg_some map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange b₄ Affine.evalEval_psi_sq Affine.Point.smul_some_eq_zero_iff Affine.Point.zsmul_some_eq_some_div"
p2m_open "WeierstrassCurve"

open Universal

scoped instance charZero_R₀ : CharZero R₀ := by
  refine charZero_of_injective_algebraMap (R := ℤ) ?_
  intro a b h
  exact MvPolynomial.C_injective (Fin 5) ℤ (by simpa using h)

theorem UIdentity_univ (n : ℤ) (hn : 1 ≤ n) : UIdentity 𝓦 n := by
  haveI : CharZero (FractionRing R₀) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R₀ (FractionRing R₀))
  exact UIdentity.of_map (algebraMap R₀ (FractionRing R₀)) (IsFractionRing.injective R₀ (FractionRing R₀))
    (InvariantDerivation.Ψ₂Sq_mul_wronskian_sq_of_charZero (𝓦.map (algebraMap R₀ (FractionRing R₀))) n hn)

theorem Psi2Sq_mul_wronskian_sq_of_one_le {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) (hn : 1 ≤ n) :
    W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
      C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
        + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) := by
  have h := (UIdentity_univ n hn).map (univHom W)
  rw [map_univHom] at h
  exact h

theorem Psi2Sq_mul_wronskian_sq' {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
      C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
        + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h := Psi2Sq_mul_wronskian_sq_of_one_le W (-n) (by omega)
    rw [Φ_neg, ΨSq_neg, Int.cast_neg, neg_sq] at h
    exact h
  · simp only [ΨSq_zero, Φ_zero, mul_zero, sub_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, map_zero, Int.cast_zero]
  · exact Psi2Sq_mul_wronskian_sq_of_one_le W n (by omega)

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.InvariantDerivation P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq.WeierstrassCurve.Universal"

open _root_.Polynomial in
theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2 =
      C ((n : R) ^ 2) * (W.ΨSq n * (C 4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n
        + C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)) :=
  WeierstrassCurve.Psi2Sq_mul_wronskian_sq' W n

end S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
end P2MW
export P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq (solution)
