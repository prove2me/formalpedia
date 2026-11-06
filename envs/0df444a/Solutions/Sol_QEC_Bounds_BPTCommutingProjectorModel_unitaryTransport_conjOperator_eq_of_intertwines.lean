-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conjOperator_eq_of_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:25:36.390347+00:00
-- url     : https://prove2.me/submissions/919fd18c-43c3-4431-a795-08dc2ad9f1ba

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (A : Semantics.Operator H)
    (B : Semantics.Operator K)
    (hintertwines : U.toLinearEquiv.toLinearMap.comp A =
      B.comp U.toLinearEquiv.toLinearMap) :
    U.conjOperator A = B := by
  apply LinearMap.ext
  intro vector
  change U.toLinearEquiv (A (U.toLinearEquiv.symm vector)) = B vector
  calc
    U.toLinearEquiv (A (U.toLinearEquiv.symm vector)) =
        B (U.toLinearEquiv (U.toLinearEquiv.symm vector)) := by
      exact congrArg (fun operator : H →ₗ[Complex] K =>
        operator (U.toLinearEquiv.symm vector)) hintertwines
    _ = B vector := by rw [U.toLinearEquiv.apply_symm_apply]
end QEC.Bounds.BPTCommutingProjectorModel
