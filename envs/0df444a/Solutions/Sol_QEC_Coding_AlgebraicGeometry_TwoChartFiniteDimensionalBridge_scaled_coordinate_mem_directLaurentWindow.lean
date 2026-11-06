-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinate_mem_directLaurentWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:21.966073+00:00
-- url     : https://prove2.me/submissions/d3f7a6eb-db8a-47a0-9571-f0bb520f4b9d

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_twoChartScaledCoordinateMap_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurentToRatFunc_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurent_directCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_direct_repr_inverse_polynomial_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_repr_smul_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_inverseBasis_coordinate_to_direct
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_mul_inverse_support_subset


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι)
    (hdirect : ∃ p : Polynomial k,
      b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) p)
    (hinverse :
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
      ∃ q : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr (d • x) j) =
          InverseChartDenominatorTransport.directLaurentToRatFunc k
            (InverseChartDenominatorTransport.inverseLaurentCoordinate k q)) :
    twoChartScaledCoordinateMap b a d x j ∈
      directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
  rcases hdirect with ⟨p, hp⟩
  have hp' : algebraMap (Polynomial k) (RatFunc k) a * b.repr x j =
      algebraMap (Polynomial k) (RatFunc k) p := by
    rw [← _root_.QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.repr_smul_polynomial
      b a x j]
    exact hp
  let oldRepr := b.repr
  obtain ⟨q, hq'⟩ : ∃ q : Polynomial k,
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j =
        InverseChartDenominatorTransport.directLaurentToRatFunc k
          (InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
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
    rcases hinverse with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) * oldRepr x j =
          oldRepr (d • x) j :=
        (direct_repr_inverse_polynomial_smul
          (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b d x j).symm
      _ = InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr (d • x) j) := by
        symm
        exact InverseChartDenominatorTransport.inverseBasis_coordinate_to_direct
          (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s) b (d • x) j
      _ = _ := hq
  let w : LaurentPolynomial k :=
    LaurentFiniteWindow.directCoordinate k p *
      InverseChartDenominatorTransport.inverseLaurentCoordinate k d
  have hwImage :
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
        twoChartScaledCoordinateMap b a d x j := by
    calc
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
          algebraMap (Polynomial k) (RatFunc k) p *
            InverseAffinePlace.rationalInvolution k
              (algebraMap (Polynomial k) (RatFunc k) d) := by
        simp [w, map_mul,
          InverseChartDenominatorTransport.directLaurent_inverseLaurentCoordinate_eq_rationalInvolution,
          directLaurent_directCoordinate]
      _ = _ := by
        rw [twoChartScaledCoordinateMap_apply]
        rw [← hp']
        ac_rfl
  have hwOther : w =
      LaurentFiniteWindow.directCoordinate k a *
        InverseChartDenominatorTransport.inverseLaurentCoordinate k q := by
    apply directLaurentToRatFunc_injective k
    calc
      InverseChartDenominatorTransport.directLaurentToRatFunc k w =
          twoChartScaledCoordinateMap b a d x j := hwImage
      _ = algebraMap (Polynomial k) (RatFunc k) a *
          InverseChartDenominatorTransport.directLaurentToRatFunc k
            (InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
        rw [twoChartScaledCoordinateMap_apply, mul_assoc, hq']
      _ = InverseChartDenominatorTransport.directLaurentToRatFunc k
          (LaurentFiniteWindow.directCoordinate k a *
            InverseChartDenominatorTransport.inverseLaurentCoordinate k q) := by
        rw [map_mul, directLaurent_directCoordinate]
  have hw : w ∈ LaurentFiniteWindow.laurentWindow k
      (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
    change w.coeff.support ⊆ Finset.Icc (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
    intro n hn
    have hlower : n ∈ Finset.Icc (-(d.natDegree : ℤ)) (p.natDegree : ℤ) := by
      apply LaurentFiniteWindow.direct_mul_inverse_support_subset k p d
      simpa only [w, InverseChartDenominatorTransport.inverseLaurentCoordinate,
        LaurentFiniteWindow.inverseCoordinate] using hn
    have hupper : n ∈ Finset.Icc (-(q.natDegree : ℤ)) (a.natDegree : ℤ) := by
      apply LaurentFiniteWindow.direct_mul_inverse_support_subset k a q
      simpa only [hwOther, InverseChartDenominatorTransport.inverseLaurentCoordinate,
        LaurentFiniteWindow.inverseCoordinate] using hn
    rw [Finset.mem_Icc] at hlower hupper ⊢
    exact ⟨hlower.1, hupper.2⟩
  exact ⟨⟨w, hw⟩, hwImage⟩
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
