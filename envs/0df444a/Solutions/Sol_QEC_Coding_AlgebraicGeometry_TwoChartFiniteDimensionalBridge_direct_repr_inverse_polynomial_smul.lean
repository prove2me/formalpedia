-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.direct_repr_inverse_polynomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:27.277128+00:00
-- url     : https://prove2.me/submissions/23b12f1b-aaa9-4f1f-abdd-9467726b0137

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [_π : Algebra (Polynomial k) F]
    [_τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (d : Polynomial k) (x : F) (j : ι) :
    let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
    let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
    let oldRepr := oldBasis.repr
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    oldRepr (d • x) j =
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j := by
  dsimp only
  let oldModule : Module (RatFunc k) F := @Algebra.toModule (RatFunc k) F _ _ ρ
  let oldBasis : @Module.Basis ι (RatFunc k) F _ _ oldModule := b
  let oldRepr := oldBasis.repr
  let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  change oldRepr
      ((@Algebra.algebraMap (RatFunc k) F _ _ ρ)
        (InverseAffinePlace.rationalInvolution k
          (algebraMap (Polynomial k) (RatFunc k) d)) * x) j =
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j
  let r := InverseAffinePlace.rationalInvolution k
    (algebraMap (Polynomial k) (RatFunc k) d)
  let hOld := ρ.smul_def' r x
  calc
    oldRepr ((@Algebra.algebraMap (RatFunc k) F _ _ ρ) r * x) j =
        oldRepr (@SMul.smul (RatFunc k) F oldModule.toSMul r x) j := by
      apply congrArg (fun z : F => oldRepr z j)
      exact hOld.symm
    _ = (r • oldRepr x) j :=
      congrArg (fun c : ι →₀ RatFunc k => c j) (oldRepr.map_smul r x)
    _ = r * oldRepr x j := by
      simp [Finsupp.smul_apply]
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
