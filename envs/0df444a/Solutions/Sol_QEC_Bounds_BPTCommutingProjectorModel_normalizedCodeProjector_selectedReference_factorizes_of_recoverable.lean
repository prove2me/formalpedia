-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_selectedReference_factorizes_of_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:36:40.483072+00:00
-- url     : https://prove2.me/submissions/a57987ca-b820-471a-8ff3-f04d7d4ec51c

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_normalizedCodeProjectorDensity_supportedOn
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_selectedReferenceMarginal_factorizes


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
    (hcorrectable : M.RegionErasureRecoverable region)
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    (M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one)) := by
  rcases hcorrectable with ⟨recovery, hrecovery⟩
  exact (M.regionSubsystem region).erasureRecovery_implies_selectedReferenceMarginal_factorizes
    M.codeSpace recovery hrecovery (M.normalizedCodeProjectorDensity hcode)
    (M.normalizedCodeProjectorDensity_supportedOn hcode) Ref purification
end QEC.Bounds.BPTCommutingProjectorModel
