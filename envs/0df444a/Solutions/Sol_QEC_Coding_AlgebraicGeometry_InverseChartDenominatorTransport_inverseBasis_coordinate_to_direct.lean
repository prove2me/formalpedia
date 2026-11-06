-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseBasis_coordinate_to_direct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:28:59.24402+00:00
-- url     : https://prove2.me/submissions/462d0207-f647-4790-b2fc-595ca05e7b2b

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
theorem _root_.solution
    [Field k] [Field F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) :
    let oldRepr := b.repr
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower (k := k) (F := F)
        (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F :=
      InverseAffinePlace.transportedIsSeparable (k := k) (F := F)
        (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ x : F, ∀ j : ι,
      InverseAffinePlace.rationalInvolution k
        ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr x j) =
        oldRepr x j := by
  dsimp only
  let oldRepr := b.repr
  let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  let : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower (k := k) (F := F)
      (oldRationalAlgebra := ρ)
  let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  intro x j
  simp [inverseBasis, Module.Basis.mapCoeffs, Finsupp.mapRange_apply]
  change InverseAffinePlace.rationalInvolution k
      ((InverseAffinePlace.rationalInvolution k).symm (oldRepr x j)) =
    oldRepr x j
  exact (InverseAffinePlace.rationalInvolution k).apply_symm_apply _
end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
