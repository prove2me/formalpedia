-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:07.070308+00:00
-- url     : https://prove2.me/submissions/6615e7b6-5a3d-49e2-a5fe-3e3ef7ee12c4

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_exists_common_denominator_direct_chart


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
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) :
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
    ∀ (L : Submodule (Polynomial k) F), Module.Finite (Polynomial k) L →
      ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι, ∃ p : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr
            (a • (x : F)) j) =
          directLaurentToRatFunc k (inverseLaurentCoordinate k p) := by
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
  dsimp only
  intro L hfinite
  let : Module.Finite (Polynomial k) L := hfinite
  obtain ⟨a, ha, hcoordinates⟩ :=
    QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
      (b := inverseBasis (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b) L
  refine ⟨a, ha, ?_⟩
  intro x j
  rcases hcoordinates x j with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [← hp]
  exact
    (directLaurent_inverseLaurentCoordinate_eq_rationalInvolution k p).symm
end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
