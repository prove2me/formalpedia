-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_region_and_externalBoundary_reference_factorize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:55:16.717128+00:00
-- url     : https://prove2.me/submissions/4d2eb056-aa76-400b-a18c-230616983316

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_normalizedCodeProjector_selectedReference_factorizes_of_recoverable

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hregion : M.RegionErasureRecoverable region)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary region))
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    ((M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) ∧
    ((M.regionSubsystem (M.externalBoundary region)).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem (M.externalBoundary region)).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) :=
  ⟨M.normalizedCodeProjector_selectedReference_factorizes_of_recoverable region hcode
      hregion Ref purification,
    M.normalizedCodeProjector_selectedReference_factorizes_of_recoverable
      (M.externalBoundary region) hcode hexternal Ref purification⟩
end QEC.Bounds.BPTCommutingProjectorModel
