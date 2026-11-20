-- Prove2me | solution 1 for QEC.Distillation.Why24AGFamily.f1024Why24OddRetainedDifferentialOrder_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:40:57.65414+00:00
-- url     : https://prove2.me/submissions/857ef949-ce06-417f-82c8-5bf0bf9c5ac1

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
namespace QEC.Distillation.Why24AGFamily
theorem _root_.solution (r : ℕ)
    (i : f1024Why24OddRetainedCandidateIndex r) :
    QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddRetainedRationalPlace r i).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) = -1 := by
  have hlower := f1024Why24OddCandidateDifferentialOrder_lower_bound r i.1
  have hresidue : f1024Why24OddCandidateResidue r i.1 ≠ 0 :=
    (Finset.mem_filter.mp i.2).2
  have hnotRegular : ¬ 0 ≤
      QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
        (k := F1024) (F := F1024TowerLevel (2 * r + 2))
        (f1024Why24OddCandidateRationalPlace r i.1).place
        (f1024Why24OddDifferential r)
        (f1024Why24OddDifferential_ne_zero r) := by
    exact fun hregular => hresidue
      ((f1024Why24OddCandidateResidue_eq_zero_iff_order_nonnegative r i.1).mpr
        hregular)
  change QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder
      (k := F1024) (F := F1024TowerLevel (2 * r + 2))
      (f1024Why24OddCandidateRationalPlace r i.1).place
      (f1024Why24OddDifferential r)
      (f1024Why24OddDifferential_ne_zero r) = -1
  omega
end QEC.Distillation.Why24AGFamily
