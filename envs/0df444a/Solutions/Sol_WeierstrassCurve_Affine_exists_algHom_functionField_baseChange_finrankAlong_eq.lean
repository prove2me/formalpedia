-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b3015788-82b4-558c-8e89-28fc2203960b

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "hfin hι mk ι"
p2m_open "WeierstrassCurve.Affine.IsogenyEndDatum WeierstrassCurve.Affine WeierstrassCurve"
private def _root_.WeierstrassCurve.Affine.IsogenyEndDatum.degree {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} (D : IsogenyEndDatum W) : ℕ :=
  AlgebraicCurve.finrankAlong F D.ι
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "degree"
end WeierstrassCurve.Affine.IsogenyEndDatum

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong FiniteAlong finrankAlong Place"
p2m_open "AlgebraicCurve"
end AlgebraicCurve
namespace CoordinateRing
end CoordinateRing
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.eq_of_valuation_isEquiv_valuation mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace ModularCurve
end ModularCurve
namespace Polynomial
p2m_export "Polynomial" "C eval₂_sub X coeff algebraMap_eq divX eval₂ aeval eval₂_add monomial basisMonomials eval₂_pow degree C_0 factor aeval_C map_map map_C map eval₂_X comp algebra eval₂_mul exists_eq_pow_rootMultiplicity_mul_and_not_dvd X_dvd_iff algHom_ext sum divX_mul_X_add flt aeval_algHom aeval_X map_monomial algebraMap_apply coe_basisMonomials ext eval₂_C funext ring ringHom_ext transcendental"
p2m_open "Polynomial"
end Polynomial
namespace Polynomial
p2m_export "Polynomial" "C eval₂_sub X coeff algebraMap_eq divX eval₂ aeval eval₂_add monomial basisMonomials eval₂_pow degree C_0 factor aeval_C map_map map_C map eval₂_X comp algebra eval₂_mul exists_eq_pow_rootMultiplicity_mul_and_not_dvd X_dvd_iff algHom_ext sum divX_mul_X_add flt aeval_algHom aeval_X map_monomial algebraMap_apply coe_basisMonomials ext eval₂_C funext ring ringHom_ext transcendental"
namespace Bivariate
p2m_open "Polynomial.Bivariate Polynomial"
end Polynomial.Bivariate
namespace TensorProduct
p2m_export "TensorProduct" "map_tmul congr lift_mk map_map smul_tmul zero_tmul sum_tmul lift mk ext tmul map Algebra.smul_def comm_tmul mk_surjective"
p2m_open "TensorProduct"
end TensorProduct
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
p2m_open "WeierstrassCurve"
end WeierstrassCurve
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"
end WeierstrassCurve.Affine
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add baseChange map_map map_zero map zero mk"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"
end WeierstrassCurve.Affine.Point

universe u v w

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"
p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"
p2m_open_scoped "TensorProduct P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.TensorProduct Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"

namespace ModularCurve

section Setup

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type v) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type w) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FF" => (W⁄F).FunctionField

def kw_coordinateRingBasis {R : Type*} [CommRing R] (V : Affine R) :
    Module.Basis (ℕ × Fin 2) R V.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis V)

end Setup

section Wire

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type v) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type w) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

variable (K : Type) [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

end Wire

end ModularCurve

end
end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.IsDedekindDomain Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"

p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong FiniteAlong finrankAlong Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext deg ofHeightOneSpectrum toValuationSubring mk"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable [Algebra K R] [IsScalarTower K R F]

theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (K := K) (R := R) (F := F)) := by
  intro w₁ w₂ h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact congrArg toValuationSubring h

end AlgebraicCurve.Place

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F] {W : Affine F}

namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "mk map basis_apply smul_basis_mul_Y"
p2m_open "WeierstrassCurve.Affine.CoordinateRing"

theorem algebraMap_eq_mk_C_C (a : F) :
    algebraMap F W.CoordinateRing a = CoordinateRing.mk W (C (C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rfl

end CoordinateRing

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing"

variable [IsDedekindDomain W.CoordinateRing]

end WeierstrassCurve.Affine

end
end

end

section
section

noncomputable section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.IsDedekindDomain"

p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong FiniteAlong finrankAlong Place"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

end AlgebraicCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"

variable {F : Type*} [Field F] {W : Affine F}

theorem algebraMap_polynomial_eq_mk_C (p : F[X]) :
    algebraMap F[X] W.CoordinateRing p = CoordinateRing.mk W (C p) :=
  rfl

end WeierstrassCurve.Affine

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"

variable {F : Type*} [Field F] (W : Affine F)

variable {W}

def yGen (W : Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

section OrdAtPoint

variable [IsDedekindDomain W.CoordinateRing]

end OrdAtPoint

section OrdVeluFun

variable {x₀ y₀ : F}

variable [IsDedekindDomain W.CoordinateRing]

end OrdVeluFun

section OrdVeluFunInfty

variable {x₀ y₀ : F} (v : AlgebraicCurve.Place F W.FunctionField)

end OrdVeluFunInfty

end WeierstrassCurve.Affine

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic]

namespace VeluPicSeam

variable {V : Affine F}

section Cases

variable [IsDedekindDomain V.CoordinateRing]

end Cases

end VeluPicSeam

end WeierstrassCurve.Affine

end
end

end

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"
p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"
p2m_open_scoped "TensorProduct P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.TensorProduct Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type u} [Field F] {W : Affine F}

theorem kw_functionField_algHom_ext {L : Type*} [Field L] [Algebra F L]
    {f g : W.FunctionField →ₐ[F] L}
    (hX : f (polyToFunctionField W X) = g (polyToFunctionField W X))
    (hy : f (yGen W) = g (yGen W)) : f = g := by
  have hCR : ∀ r : W.CoordinateRing,
      f (algebraMap W.CoordinateRing W.FunctionField r)
        = g (algebraMap W.CoordinateRing W.FunctionField r) := by
    intro r
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
    have hFX : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c)) :=
      fun c => DFunLike.congr_fun
        (Polynomial.algHom_ext (f := (f.comp (IsScalarTower.toAlgHom F W.CoordinateRing
            W.FunctionField)).comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing))
          (g := (g.comp (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)).comp
            (IsScalarTower.toAlgHom F F[X] W.CoordinateRing)) hX) c
    have hFX' : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c)))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c))) := fun c => by
      rw [show AdjoinRoot.mk W.polynomial (C c) = algebraMap F[X] W.CoordinateRing c from rfl]
      exact hFX c
    have hy' : f (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y))
        = g (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y)) := hy
    induction p using Polynomial.induction_on with
    | C c => exact hFX' c
    | monomial n c _ => simp only [map_mul, map_pow, hy', hFX' c]
    | add p q hp hq => simp only [map_add, hp, hq]
  refine AlgHom.ext fun a => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) a
  simp only [map_div₀, hCR p, hCR q]

end WeierstrassCurve.Affine

namespace ModularCurve

section Setup

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type v) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type w) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FracHom

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

end FracHom

end Setup

section Wire

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (K : Type) [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

end Wire

end ModularCurve

end
end

end

section
section

set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine"

p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing"

variable {F : Type u} [Field F]

section PointPullbackTo

variable {W : Affine F} {L : Type*} [Field L] [Algebra F L]

theorem eval₂_polynomial_of_equation_map_target {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.polynomial.eval₂
      (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP = 0 := by
  rw [equation_iff'] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination h

def pointPullbackCoordHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.CoordinateRing →ₐ[F] L where
  __ := AdjoinRoot.lift
    (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom
    yP (eval₂_polynomial_of_equation_map_target h)
  commutes' c := by
    show AdjoinRoot.lift _ _ (eval₂_polynomial_of_equation_map_target h) (algebraMap F _ c)
      = algebraMap F L c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

theorem pointPullbackCoordHomTo_mk {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) (g : F[X][Y]) :
    pointPullbackCoordHomTo h (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_equation_map_target h) g

theorem pointPullbackCoordHomTo_comp_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    (pointPullbackCoordHomTo h).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom := by
  refine RingHom.ext fun p => ?_
  show pointPullbackCoordHomTo h (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]

theorem pointPullbackCoordHomTo_injective {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    Function.Injective (pointPullbackCoordHomTo h) := by
  have hker : RingHom.ker (pointPullbackCoordHomTo h).toRingHom = ⊥ := by
    haveI : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_comap_eq_bot (R := F[X]) ?_
    rw [RingHom.comap_ker, pointPullbackCoordHomTo_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact hx
  exact (RingHom.injective_iff_ker_eq_bot (pointPullbackCoordHomTo h).toRingHom).mpr hker

def pointPullbackHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHomTo_injective h hx)

theorem pointPullbackHomTo_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) (r : W.CoordinateRing) :
    pointPullbackHomTo h hx (algebraMap W.CoordinateRing W.FunctionField r)
      = pointPullbackCoordHomTo h r :=
  IsFractionRing.lift_algebraMap (pointPullbackCoordHomTo_injective h hx) r

theorem pointPullbackHomTo_polyToFunctionField_X {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (polyToFunctionField W X) = xP := by
  rw [polyToFunctionField_apply, pointPullbackHomTo_algebraMap,
    algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]
  exact Polynomial.aeval_X _

theorem pointPullbackHomTo_yGen {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (yGen W) = yP := by
  show pointPullbackHomTo h hx (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [pointPullbackHomTo_algebraMap, pointPullbackCoordHomTo_mk]
  exact eval₂_X _ _

end PointPullbackTo

section AddMu

variable (W : Affine F)

end AddMu

end WeierstrassCurve.Affine

namespace ModularCurve

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine"

end ModularCurve

end

end

end

section
section

noncomputable section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.IsDedekindDomain"

p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"

variable {F : Type u} [Field F]

section GenericPoint

variable {W : Affine F}

theorem polyToFunctionField_eq_aeval (p : F[X]) :
    polyToFunctionField W p = Polynomial.aeval (polyToFunctionField W X) p := by
  have h1 : (polyToFunctionField W : F[X] →+* W.FunctionField)
      = algebraMap F[X] W.FunctionField :=
    (IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField).symm
  have h2 : (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField)
      = Polynomial.aeval (polyToFunctionField W X) := by
    refine Polynomial.algHom_ext ?_
    rw [Polynomial.aeval_X, IsScalarTower.coe_toAlgHom', ← h1]
  calc polyToFunctionField W p = algebraMap F[X] W.FunctionField p := by rw [h1]
    _ = (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField) p := rfl
    _ = Polynomial.aeval (polyToFunctionField W X) p := by rw [h2]

theorem equation_map_polyToFunctionField_yGen :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (polyToFunctionField W X) (yGen W) := by
  rw [equation_iff]
  have hrel := smul_basis_mul_Y (W' := W) 0 1
  rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at hrel
  have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) hrel
  rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  simp only [map_add, map_mul, map_pow, polyToFunctionField_C] at h2
  rw [show yGen W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
    from rfl]
  simp only [polyToFunctionField_apply] at h2 ⊢
  linear_combination h2

end GenericPoint

section CoordinateIdentification

variable {W : Affine F} {x₀ y₀ : F}

end CoordinateIdentification

section Transcendence

variable [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] {x₀ y₀ : F}

end Transcendence

section Certificate

variable {W : Affine F} {x₀ y₀ : F}

end Certificate

section Inclusion

variable [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] {x₀ y₀ : F}

end Inclusion

section Integrality

variable [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] {x₀ y₀ : F}

end Integrality

section Assembly

variable [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {W : Affine F} [W.IsElliptic] {x₀ y₀ : F}

end Assembly

end WeierstrassCurve.Affine

end
end

end

section
section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.Point"

p2m_open_scoped "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map mk Jacobian IsIntegral toAffine Affine.Point map_a₆ map_a₁ map_a₄ Δ Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point.add Equation equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_smul CoordinateRing.basis addY equation_iff polynomial IsogenyEndDatum polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"

variable {F : Type u} [Field F]

section TranslationCoords

variable (W : Affine F) (a b : F)

local notation "ι" => algebraMap F W.FunctionField

end TranslationCoords

section GenericPointGroup

variable {W : Affine F}

local notation "ι" => algebraMap F W.FunctionField

end GenericPointGroup

section CoordHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

end CoordHom

section AdjoinSurjective

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

theorem transcendental_polyToFunctionField_X :
    Transcendental F (polyToFunctionField W X) := by
  rw [transcendental_iff]
  intro p hp
  rw [← polyToFunctionField_eq_aeval] at hp
  exact polyToFunctionField_injective (by simpa using hp)

end AdjoinSurjective

section TranslationHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

variable (hΔ : W.Δ ≠ 0)

end TranslationHom

end WeierstrassCurve.Affine

end

end

end

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"
p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"
p2m_open_scoped "TensorProduct P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.TensorProduct Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial.Bivariate"

namespace ModularCurve

section Setup

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

theorem kw_transcendental_polyToFunctionField_X_over_baseGeneral :
    Transcendental F (polyToFunctionField (W⁄F') X) :=
  Transcendental.of_tower_top F (L := F')
    (transcendental_polyToFunctionField_X (W := (W⁄F')))

theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneral :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) := by
  have hcurve : (W⁄F).map (algebraMap F (W⁄F').FunctionField)
      = (W⁄F').map (algebraMap F' (W⁄F').FunctionField) := by
    show (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
    exact ((IsScalarTower.algebraMap_eq R₀ F (W⁄F').FunctionField).symm).trans
      (IsScalarTower.algebraMap_eq R₀ F' (W⁄F').FunctionField)
  exact hcurve ▸ equation_map_polyToFunctionField_yGen (W := (W⁄F'))

set_option maxHeartbeats 51200000 in
set_option synthInstance.maxHeartbeats 3200000 in
def kw_functionFieldMapAlongGeneral : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneral W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneral W F F') p
        hp)

theorem kw_functionFieldMapAlongGeneral_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldMapAlongGeneral_yGen :
    kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F)) = yGen (W⁄F') :=
  pointPullbackHomTo_yGen _ _

def KwFunctionFieldTensorIsDomainGeneral : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_isScalarTower_base_right_tensorGeneral :
    IsScalarTower R₀ F' ((W⁄F).FunctionField ⊗[F] F') := by
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
  rw [RingHom.comp_apply, Algebra.TensorProduct.right_algebraMap_apply,
    IsScalarTower.algebraMap_apply R₀ F F',
    show algebraMap R₀ ((W⁄F).FunctionField ⊗[F] F') r
      = (algebraMap F ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F r) from
        IsScalarTower.algebraMap_apply R₀ F ((W⁄F).FunctionField ⊗[F] F') r,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

section FracHom

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

scoped instance kw_isScalarTower_base_right_fracTensorGeneral :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R₀ ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) r).trans <|
      (congrArg (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
        (IsScalarTower.algebraMap_apply R₀ F' ((W⁄F).FunctionField ⊗[F] F') r)).trans
      (IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F' r)).symm

theorem kw_equation_tensorFracXYGeneral :
    ((W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))).toAffine.Equation
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((yGen (W⁄F)) ⊗ₜ[F] (1 : F'))) := by
  have hcurve : (W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
      = W⁄(FractionRing ((W⁄F).FunctionField ⊗[F] F')) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]; congr 1
    exact (IsScalarTower.algebraMap_eq R₀ F'
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).symm
  rw [hcurve]
  exact Equation.baseChange (W := W) (S := R₀)
    (f := (IsScalarTower.toAlgHom R₀ ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F) (S := R₀)))
    (equation_map_polyToFunctionField_yGen (W := (W⁄F)))

theorem kw_transcendental_tensorFracXGeneral :
    Function.Injective (Polynomial.aeval (R := F')
      (algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))) := by
  rw [show algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F'))
      = IsScalarTower.toAlgHom F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) from rfl,
    Polynomial.aeval_algHom]
  refine (IsFractionRing.injective ((W⁄F).FunctionField ⊗[F] F')
    (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp ?_
  have heq : (Polynomial.aeval (R := F')
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')
          : (W⁄F).FunctionField ⊗[F] F')).toRingHom
      = ((Algebra.TensorProduct.map
            (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
            (AlgHom.id F F')).toRingHom.comp
          (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
          (polyEquivTensor' F F').toAlgHom.toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · show aeval _ (C c) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' (C c)))
      rw [show (polyEquivTensor' F F') (C c) = c ⊗ₜ[F] (1 : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_C]; rfl,
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_C,
        Algebra.TensorProduct.right_algebraMap_apply, AlgHom.coe_id, id_eq, map_one]
    · show aeval _ (X : F'[X]) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' X))
      rw [show (polyEquivTensor' F F') X = (1:F') ⊗ₜ[F] (X : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_X],
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_X,
        AlgHom.coe_id, id_eq, Polynomial.aeval_X]
  have hinj : Function.Injective
      (((Algebra.TensorProduct.map
          (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
          (AlgHom.id F F')).toRingHom.comp
        (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
        (polyEquivTensor' F F').toAlgHom.toRingHom) :=
    ((Module.Flat.rTensor_preserves_injective_linearMap (M := F')
        (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X)).toLinearMap
        ((injective_iff_map_eq_zero _).mpr fun p hp =>
          transcendental_iff.mp (transcendental_polyToFunctionField_X (W := (W⁄F))) p hp)).comp
      (Algebra.TensorProduct.comm F F' F[X]).injective).comp (polyEquivTensor' F F').injective
  intro p q hpq
  refine hinj ?_
  have := DFunLike.congr_fun heq
  exact (this p).symm.trans (hpq.trans (this q))

set_option maxHeartbeats 51200000 in
set_option synthInstance.maxHeartbeats 3200000 in
def kw_functionFieldTensorFracHomGeneral :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  pointPullbackHomTo (kw_equation_tensorFracXYGeneral W F F')
    (kw_transcendental_tensorFracXGeneral W F F')

theorem kw_functionFieldTensorFracHomGeneral_X :
    kw_functionFieldTensorFracHomGeneral W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldTensorFracHomGeneral_yGen :
    kw_functionFieldTensorFracHomGeneral W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_yGen _ _

theorem kw_functionFieldTensorFracHomGeneral_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneral W F F') := by
  refine ⟨(kw_functionFieldTensorFracHomGeneral W F F').injective, ?_⟩
  set ψ := kw_functionFieldTensorFracHomGeneral W F F'
  have hκ : (ψ.restrictScalars F).comp (kw_functionFieldMapAlongGeneral W F F')
      = (IsScalarTower.toAlgHom F ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F)) := by
    refine kw_functionField_algHom_ext ?_ ?_
    · show ψ (kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)) = _
      rw [kw_functionFieldMapAlongGeneral_polyToFunctionField_X,
        kw_functionFieldTensorFracHomGeneral_X]
      rfl
    · show ψ (kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F))) = _
      rw [kw_functionFieldMapAlongGeneral_yGen, kw_functionFieldTensorFracHomGeneral_yGen]
      rfl
  have hT_sub : ∀ t : (W⁄F).FunctionField ⊗[F] F',
      algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing _) t ∈ ψ.toRingHom.fieldRange := by
    intro t
    induction t with
    | zero => simp only [_root_.map_zero]; exact zero_mem _
    | add _ _ hx hy => simp only [map_add]; exact add_mem hx hy
    | tmul a c =>
      rw [show (a ⊗ₜ[F] c : (W⁄F).FunctionField ⊗[F] F') = (a ⊗ₜ[F] 1) * (1 ⊗ₜ[F] c) from
            by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul]
      refine mul_mem ?_ ⟨algebraMap F' _ c, ?_⟩
      · exact ⟨kw_functionFieldMapAlongGeneral W F F' a, DFunLike.congr_fun hκ a⟩
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ.commutes,
          IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
  intro z
  obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective
    (A := (W⁄F).FunctionField ⊗[F] F') (K := FractionRing _) z
  exact div_mem (hT_sub t) (hT_sub s)

def kw_functionFieldTensorFracEquivGeneral :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  AlgEquiv.ofBijective _ (kw_functionFieldTensorFracHomGeneral_bijective W F F')

def kw_tensorIotaRingHomGeneral (D : IsogenyEndDatum (W⁄F)) :
    (W⁄F).FunctionField ⊗[F] F' →+* (W⁄F).FunctionField ⊗[F] F' :=
  (Algebra.TensorProduct.map D.ι (AlgHom.id F F')).toRingHom

theorem kw_tensorIotaRingHomGeneral_tmul (D : IsogenyEndDatum (W⁄F)) (a : (W⁄F).FunctionField)
    (c : F') : kw_tensorIotaRingHomGeneral W F F' D (a ⊗ₜ[F] c) = (D.ι a) ⊗ₜ[F] c := by
  simp [kw_tensorIotaRingHomGeneral, Algebra.TensorProduct.map_tmul]

theorem kw_tensorIotaRingHomGeneral_injective (D : IsogenyEndDatum (W⁄F)) :
    Function.Injective (kw_tensorIotaRingHomGeneral W F F' D) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') D.ι.toLinearMap D.ι.injective

def kw_tensorFracIotaRingHomGeneral (D : IsogenyEndDatum (W⁄F)) :
    FractionRing ((W⁄F).FunctionField ⊗[F] F')
      →+* FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (L := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (kw_tensorIotaRingHomGeneral_injective W F F' D)

theorem kw_tensorFracIotaRingHomGeneral_algebraMap (D : IsogenyEndDatum (W⁄F))
    (t : (W⁄F).FunctionField ⊗[F] F') :
    kw_tensorFracIotaRingHomGeneral W F F' D
        (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')) t)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          (kw_tensorIotaRingHomGeneral W F F' D t) := by
  unfold kw_tensorFracIotaRingHomGeneral IsFractionRing.map
  exact IsLocalization.map_eq (T := nonZeroDivisors ((W⁄F).FunctionField ⊗[F] F')) _ t

def KwTensorFracIotaFinrankSeamGeneral : Prop :=
  ∀ D : IsogenyEndDatum (W⁄F),
    (kw_tensorFracIotaRingHomGeneral W F F' D).Finite ∧
    (letI := (kw_tensorFracIotaRingHomGeneral W F F' D).toAlgebra
     @Module.finrank (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
       (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _ Algebra.toModule) = D.degree

def kw_isogenyEndDatumBaseChangeIotaGeneral (D : IsogenyEndDatum (W⁄F)) :
    (W⁄F').FunctionField →ₐ[F'] (W⁄F').FunctionField :=
  let ψ := kw_functionFieldTensorFracEquivGeneral W F F'
  { ψ.symm.toRingEquiv.toRingHom.comp
      ((kw_tensorFracIotaRingHomGeneral W F F' D).comp ψ.toRingEquiv.toRingHom) with
    commutes' := fun c => by
      have hc : ψ (algebraMap F' (W⁄F').FunctionField c)
          = algebraMap ((W⁄F).FunctionField ⊗[F] F')
              (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
              ((1 : (W⁄F).FunctionField) ⊗ₜ[F] c) := by
        rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
      show ψ.symm (kw_tensorFracIotaRingHomGeneral W F F' D (ψ (algebraMap F' _ c)))
          = algebraMap F' _ c
      rw [hc, kw_tensorFracIotaRingHomGeneral_algebraMap, kw_tensorIotaRingHomGeneral_tmul,
        map_one, ← hc]
      exact ψ.symm_apply_apply _ }

def KwIsogenyEndDatumBaseChangeAlongGeneral (_σ : F →ₐ[R₀] F') (N : ℕ) : Prop :=
  (∃ D : IsogenyEndDatum (W⁄F), D.degree = N) →
    ∃ D' : IsogenyEndDatum (W⁄F'), D'.degree = N

theorem kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneral
    (hseam : KwTensorFracIotaFinrankSeamGeneral W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) : KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N := by
  intro ⟨D, hD⟩
  let ψ := kw_functionFieldTensorFracEquivGeneral W F F'
  let ιFr := kw_tensorFracIotaRingHomGeneral W F F' D
  obtain ⟨hfin_Fr, hdeg_Fr⟩ := hseam D
  have hcomm : ∀ x, ιFr (ψ x) = ψ (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D x) :=
    fun x => (ψ.apply_symm_apply _).symm
  have hfin : (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D).toRingHom.Finite := by
    have h₁ : (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D).toRingHom
        = ψ.symm.toRingEquiv.toRingHom.comp (ιFr.comp ψ.toRingEquiv.toRingHom) := rfl
    rw [h₁]
    exact (RingHom.Finite.of_surjective _ ψ.symm.surjective).comp
      (hfin_Fr.comp (RingHom.Finite.of_surjective _ ψ.surjective))
  refine ⟨⟨kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D, hfin.to_isIntegral, hfin⟩, ?_⟩
  refine hD ▸ ?_
  exact (@Algebra.finrank_eq_of_equiv_equiv
      (W⁄F').FunctionField (W⁄F').FunctionField _ _
      (algebraAlong (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _
      (ιFr.toAlgebra) ψ.toRingEquiv ψ.toRingEquiv
      (RingHom.ext hcomm)).trans hdeg_Fr

end FracHom

theorem kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneral
    (htens : KwFunctionFieldTensorIsDomainGeneral W F F')
    (hseam : haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
             KwTensorFracIotaFinrankSeamGeneral W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
  kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneral W F F' hseam σ N

end Setup

section SatGate

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

end SatGate

end ModularCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"
end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve AlgebraicCurve P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve"
p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"
p2m_open_scoped "TensorProduct P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.TensorProduct Polynomial P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.Polynomial"

namespace ModularCurve

section Setup

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section FFDomain

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

theorem kw_coordinateRingMap_basisGeneral (i : ℕ × Fin 2) :
    CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
        (kw_coordinateRingBasis (W⁄F).toAffine i)
      = kw_coordinateRingBasis ((W⁄F).toAffine.map (algebraMap F F')) i := by
  obtain ⟨n, j⟩ := i
  simp only [kw_coordinateRingBasis, Module.Basis.smulTower_apply,
    Polynomial.coe_basisMonomials, CoordinateRing.map_smul]
  congr 1
  · simp [Polynomial.map_monomial]
  · rcases j with ⟨j, hj⟩
    interval_cases j <;>
      simp [CoordinateRing.basis_apply, CoordinateRing.map,
        AdjoinRoot.lift_root, AdjoinRoot.powerBasis'_gen]

def kw_coordinateRingMapAlongGeneral :
    CR →ₐ[F] ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing where
  __ := CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    show CoordinateRing.map (W⁄F).toAffine (algebraMap F F') (algebraMap F CR r) = algebraMap F _ r
    rw [IsScalarTower.algebraMap_apply F F[X] CR,
      show (algebraMap F F[X] r) = Polynomial.C r from rfl,
      show (algebraMap F[X] CR) (C r) = (C r : F[X]) • (1 : CR) by
        rw [Algebra.smul_def, mul_one],
      CoordinateRing.map_smul, map_one, Polynomial.map_C,
      IsScalarTower.algebraMap_apply F F' ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      IsScalarTower.algebraMap_apply F' F'[X]
        ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      show (algebraMap F' F'[X]) ((algebraMap F F') r) = Polynomial.C ((algebraMap F F') r)
        from rfl,
      Algebra.smul_def, mul_one]

theorem kw_coordinateRingTensor_isDomainGeneral : IsDomain (CR ⊗[F] F') := by
  suffices h : IsDomain (F' ⊗[F] CR) by
    haveI := h
    exact Function.Injective.isDomain (Algebra.TensorProduct.comm F CR F').toRingHom
      (Algebra.TensorProduct.comm F CR F').injective
  set W'' := (W⁄F).toAffine.map (algebraMap F F') with hW''
  let θ : F' ⊗[F] CR →ₐ[F'] W''.CoordinateRing :=
    AlgHom.liftEquiv F F' CR W''.CoordinateRing (kw_coordinateRingMapAlongGeneral W F F')
  have hθ : Function.Injective θ := by
    let bT : Module.Basis (ℕ × Fin 2) F' (F' ⊗[F] CR) :=
      Algebra.TensorProduct.basis F' (kw_coordinateRingBasis (W⁄F).toAffine)
    let bD : Module.Basis (ℕ × Fin 2) F' W''.CoordinateRing := kw_coordinateRingBasis W''
    have key : ∀ i, θ.toLinearMap (bT i) = (bT.equiv bD (Equiv.refl _)) (bT i) := fun i => by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
      simp only [bT, Algebra.TensorProduct.basis_apply, θ, AlgHom.liftEquiv_tmul, one_smul]
      exact kw_coordinateRingMap_basisGeneral W F F' i
    have heq : (θ : F' ⊗[F] CR → W''.CoordinateRing) = bT.equiv bD (Equiv.refl _) :=
      funext fun x => DFunLike.congr_fun (bT.ext key : θ.toLinearMap = _) x
    exact heq ▸ (bT.equiv bD (Equiv.refl _)).injective
  exact Function.Injective.isDomain θ.toRingHom hθ

theorem kw_functionFieldTensorIsDomain_dischargeGeneral :
    KwFunctionFieldTensorIsDomainGeneral W F F' := by
  show IsDomain (FFₗ ⊗[F] F')
  haveI hCR : IsDomain (CR ⊗[F] F') := kw_coordinateRingTensor_isDomainGeneral W F F'
  letI : Algebra (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ)
      (AlgHom.id F F')).toRingHom.toAlgebra
  haveI hst : IsScalarTower CR (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    IsScalarTower.of_algebraMap_eq (R := CR) (S := CR ⊗[F] F') (A := FFₗ ⊗[F] F') fun c => by
      show Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ) (AlgHom.id F F')
          (algebraMap CR (CR ⊗[F] F') c) = algebraMap CR (FFₗ ⊗[F] F') c
      rfl
  haveI hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) (FFₗ ⊗[F] F') :=
    IsLocalization.tensorProduct_tensorProduct F F' (nonZeroDivisors CR) FFₗ (by
      ext x; simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul])
  have hle : Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)
      ≤ nonZeroDivisors (CR ⊗[F] F') := by
    rintro _ ⟨c, hc, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hinj : Function.Injective (algebraMap CR (CR ⊗[F] F')) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F F').injective
    exact fun h => (nonZeroDivisors.ne_zero hc) (hinj (by simp only [_root_.map_zero] at h ⊢; exact h))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) _ hle

end FFDomain
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

section Seam

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

theorem kw_tensorIotaRingHom_finiteGeneral (D : IsogenyEndDatum (W⁄F)) :
    (kw_tensorIotaRingHomGeneral W F F' D).Finite :=
  RingHom.Finite.tensorProductMap (f := D.ι) D.hfin (g := AlgHom.id F F') (RingHom.Finite.id F')

theorem kw_tensorFracIotaFinrankSeam_dischargeGeneral :
    KwTensorFracIotaFinrankSeamGeneral W F F' := by
  classical
  intro D
  let FF := (W⁄F).FunctionField
  let T := (W⁄F).FunctionField ⊗[F] F'
  let FrT := FractionRing ((W⁄F).FunctionField ⊗[F] F')
  let ιT : T →+* T := kw_tensorIotaRingHomGeneral W F F' D
  let ιFr : FrT →+* FrT := kw_tensorFracIotaRingHomGeneral W F F' D
  have hιT_inj : Function.Injective ιT := kw_tensorIotaRingHomGeneral_injective W F F' D
  have hιT_fin : ιT.Finite := kw_tensorIotaRingHom_finiteGeneral W F F' D
  have hιFr_am : ∀ t : T, ιFr (algebraMap T FrT t) = algebraMap T FrT (ιT t) :=
    kw_tensorFracIotaRingHomGeneral_algebraMap W F F' D
  letI algDι : Algebra FF FF := D.ι.toRingHom.toAlgebra
  letI smulDι : SMul FF FF := algDι.toSMul
  letI modDι : Module FF FF := Algebra.toModule
  have hsmul_Dι : ∀ (c x : FF), c • x = D.ι c * x := fun c x => rfl
  haveI hfinFF : Module.Finite FF FF := D.hfin
  haveI hfreeFF : Module.Free FF FF := Module.Free.of_divisionRing FF FF
  let b : Module.Basis (Fin D.degree) FF FF :=
    Module.finBasisOfFinrankEq FF FF (n := D.degree) rfl
  have hrepr_mul : ∀ (c x : FF) (j : Fin D.degree),
      b.repr (D.ι c * x) j = c * b.repr x j := fun c x j => by
    rw [← hsmul_Dι, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e : Fin D.degree → T := fun i => (b i) ⊗ₜ[F] (1 : F')
  let bFr : Fin D.degree → FrT := fun i => algebraMap T FrT (e i)
  have hspanT : ∀ t : T, ∃ c : Fin D.degree → T, t = ∑ i, ιT (c i) * e i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨cx, hx⟩ := hx; obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by simp only [Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, ← hx, ← hy]⟩
    | tmul a c =>
      refine ⟨fun i => (b.repr a i) ⊗ₜ[F] c, ?_⟩
      have hb_sum : a = ∑ i, D.ι (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_Dι, _root_.map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_Dι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, D.ι (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [kw_tensorIotaRingHomGeneral_tmul W F F' D,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin D.degree → T, ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF f) x j
          rwa [D.ι.commutes] at h }
    let Ej : T →ₗ[F] T := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T) (i : Fin D.degree),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF) ⊗ₜ[F] c') = (D.ι x) ⊗ₜ[F] c' from
              kw_tensorIotaRingHomGeneral_tmul W F F' D _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        show (pj (D.ι x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF) ⊗ₜ[F] c' else 0
        rw [show pj (D.ι x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · show b.repr (D.ι x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp [h]
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, _root_.map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc'
  have hint : ∀ s : T, s ≠ 0 → ∃ (u s₀ : T), s₀ ≠ 0 ∧ s * u = ιT s₀ := by
    intro s hs
    obtain ⟨p, hp_monic, hp_eval⟩ : ιT.IsIntegralElem s := hιT_fin.to_isIntegral s
    obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p
      hp_monic.ne_zero 0
    simp only [Polynomial.C_0, sub_zero] at hq_eq hq_ndvd
    have hq0 : q.coeff 0 ≠ 0 := fun h => hq_ndvd (Polynomial.X_dvd_iff.mpr h)
    have hqs : q.eval₂ ιT s = 0 := by
      have h := hp_eval
      rw [hq_eq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        mul_eq_zero] at h
      exact h.resolve_left (pow_ne_zero _ hs)
    have h3 : ιT (q.coeff 0) + s * (q.divX).eval₂ ιT s = 0 := by
      have h := hqs
      conv at h => lhs; rw [← Polynomial.divX_mul_X_add q]
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, add_comm, mul_comm] using h
    exact ⟨(q.divX).eval₂ ιT s, -q.coeff 0, neg_ne_zero.mpr hq0,
      by rw [_root_.map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : Fin D.degree → FrT, z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (_root_.map_zero ιT).symm))
    have hu_ne : u ≠ 0 := fun h => hιTs₀ (by rw [← hsu, h, mul_zero])
    obtain ⟨c, hc⟩ := hspanT (t * u)
    refine ⟨fun i => (algebraMap T FrT s₀)⁻¹ * algebraMap T FrT (c i), ?_⟩
    have hum := (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr hu_ne
    have hz : (algebraMap T FrT t) / (algebraMap T FrT s)
        = (algebraMap T FrT (ιT s₀))⁻¹ * algebraMap T FrT (t * u) := by
      rw [← div_eq_inv_mul, ← hsu, map_mul, map_mul,
        ← div_mul_div_comm, div_self hum, mul_one]
    rw [hz, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hιFr_am s₀, ← hιFr_am (c i), ← map_inv₀ ιFr, mul_assoc]
  have hliFr : ∀ d : Fin D.degree → FrT, ∑ i, ιFr (d i) * bFr i = 0 → ∀ j, d j = 0 := by
    intro d hd j
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors T) (Finset.univ.image d)
    choose p hp using fun i => hq (d i) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    have hq0 : (algebraMap T FrT (q : T)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr (nonZeroDivisors.ne_zero q.2)
    have hp' : ∀ i, algebraMap T FrT (p i) = algebraMap T FrT (q : T) * d i := fun i => by
      rw [hp i, Algebra.smul_def]
    have hd' : algebraMap T FrT (∑ i, ιT (p i) * e i) = 0 := by
      have h1 : ∑ i, ιFr (algebraMap T FrT (q : T)) * (ιFr (d i) * bFr i) = 0 := by
        rw [← Finset.mul_sum, hd, mul_zero]
      rw [map_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hιFr_am (p i), ← mul_assoc, ← map_mul, ← hp' i]
    have hpj : p j = 0 :=
      hliT p ((IsFractionRing.injective T FrT) (by simpa using hd')) j
    have hthis : algebraMap T FrT (q : T) * d j = 0 := by
      rw [← hp' j, hpj, _root_.map_zero]
    exact (mul_eq_zero.mp hthis).resolve_left hq0
  letI algFr : Algebra FrT FrT := ιFr.toAlgebra
  letI smulFr : SMul FrT FrT := algFr.toSMul
  letI modFr : Module FrT FrT := Algebra.toModule
  have hsmul_Fr : ∀ (c x : FrT), c • x = ιFr c * x := fun c x => rfl
  have hli_modFr : LinearIndependent FrT bFr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine hliFr g ?_ i
    simpa only [hsmul_Fr] using hg
  have hsp_modFr : ⊤ ≤ Submodule.span FrT (Set.range bFr) := by
    intro z _
    obtain ⟨d, hd⟩ := hspanFr z
    rw [hd]
    exact Submodule.sum_mem _ fun i _ => (hsmul_Fr (d i) (bFr i)) ▸
      Submodule.smul_mem _ (d i) (Submodule.subset_span ⟨i, rfl⟩)
  let bFr' : Module.Basis (Fin D.degree) FrT FrT := .mk hli_modFr hsp_modFr
  refine ⟨Module.Finite.of_basis bFr', ?_⟩
  show Module.finrank FrT FrT = D.degree
  rw [Module.finrank_eq_card_basis bFr', Fintype.card_fin]

end Seam
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

theorem kw_isogenyEndDatumBaseChangeAlong_dischargeGeneral (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') :=
    kw_functionFieldTensorIsDomain_dischargeGeneral W F F'
  kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneral W F F'
    (kw_functionFieldTensorIsDomain_dischargeGeneral W F F')
    (kw_tensorFracIotaFinrankSeam_dischargeGeneral W F F') σ N

end Setup
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

section SatGate

variable (W : WeierstrassCurve ℚ) [W.IsElliptic]
variable (F : Type) [Field F] [Algebra ℚ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type) [Field F'] [Algebra ℚ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower ℚ F F']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

end SatGate
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"
end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.ModularCurve"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine _root_.AlgebraicCurve _root_.P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.AlgebraicCurve in
theorem solution
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    (ι : (W.baseChange F).toAffine.FunctionField →ₐ[F] (W.baseChange F).toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    ∃ ι' : (W.baseChange F').toAffine.FunctionField →ₐ[F'] (W.baseChange F').toAffine.FunctionField,
      ι'.toRingHom.IsIntegral ∧ ∃ hfin' : FiniteAlong F' ι', finrankAlong F' ι' = finrankAlong F ι := by
  obtain ⟨D', hD'⟩ := ModularCurve.kw_isogenyEndDatumBaseChangeAlong_dischargeGeneral W F F'
    (IsScalarTower.toAlgHom R₀ F F') (finrankAlong F ι) ⟨⟨ι, hι, hfin⟩, rfl⟩
  exact ⟨D'.ι, D'.hι, D'.hfin, hD'⟩

end
end S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq (solution)
