-- Prove2me | solution 1 for QEC.Distillation.Why24AGFamily.f1024Why24OddCSSZDistance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:44:06.47418+00:00
-- url     : https://prove2.me/submissions/77a4e81d-455a-428e-8cb3-4b995fbdec1a

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddStabilizerCode_dual_distance_lower_bound
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
import Theorems.Thm_QEC_Coding_HypergraphProduct_le_finitePredicateMinimum


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.Why24AGFamily
open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial
noncomputable section
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF2CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF3CharTwo
attribute [instance] F1024TowerStageData.fieldInst
  F1024TowerStageData.rationalAlgebraInst
  F1024TowerStageData.finiteDimensionalInst
  F1024TowerStageData.separableInst
  F1024TowerStageData.constantAlgebraInst
  F1024TowerStageData.constantRationalTowerInst
  F1024TowerStageData.polynomialAlgebraInst
  F1024TowerStageData.polynomialRationalTowerInst
  F1024TowerStageData.charTwoInst
attribute [instance] F1024TowerFiniteChartData.commRingInst
  F1024TowerFiniteChartData.domainInst
  F1024TowerFiniteChartData.dedekindInst
  F1024TowerFiniteChartData.constantAlgebraInst
  F1024TowerFiniteChartData.actualAlgebraInst
  F1024TowerFiniteChartData.constantTowerInst
  F1024TowerFiniteChartData.fractionRingInst
open QEC.Coding.AlgebraicGeometry
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower
open QEC.Distillation.Why24WeightedTriorthogonalCSS
namespace QEC.Distillation.Why24AGFamily
theorem _root_.solution (r : ℕ) :
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
      (f1024Why24OddWeightedMatrix r).cssZDistance := by
  classical
  rw [QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.cssZDistance]
  apply QEC.Coding.HypergraphProduct.le_finitePredicateMinimum
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    exact hx.2 (Submodule.zero_mem _)
  calc
    (selectedDistanceLowerBound (oddGenus r) : WithTop ℕ) ≤
        QEC.Coding.HypergraphProduct.extendedMinimumDistance
          (f1024Why24OddWeightedMatrix r).stabilizerCode.dual :=
      f1024Why24OddStabilizerCode_dual_distance_lower_bound r
    _ ≤ (QEC.Coding.HammingWeight x : WithTop ℕ) := by
      rw [QEC.Coding.HypergraphProduct.extendedMinimumDistance]
      exact QEC.Coding.HypergraphProduct.finitePredicateMinimum_le_of
        ⟨hx.1, hx0⟩
end QEC.Distillation.Why24AGFamily
