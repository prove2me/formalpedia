-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_conjOperator_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:41:25.098356+00:00
-- url     : https://prove2.me/submissions/9e1a499e-ac4d-494e-87a3-89b5026ce906

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjOperator_compression_of_intertwining

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
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))) :
    (LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
        (((fourFactorBCUnitaryTransport (A := A) (D := D) E).conjOperator P).comp
          (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)) =
      (jointBCSectorActiveUnitary (A := A) pB pC V).conjOperator
        ((LinearMap.adjoint (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)).comp
          (P.comp (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC))) := by
  exact conjOperator_compression_of_intertwining
    (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC)
    (fourFactorBCUnitaryTransport (A := A) (D := D) E)
    (jointBCSectorActiveUnitary (A := A) pB pC V)
    (fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
      (A := A) (D := D) pB pC E V hintertwines) P
end QEC.Bounds.BPTCommutingProjectorModel
