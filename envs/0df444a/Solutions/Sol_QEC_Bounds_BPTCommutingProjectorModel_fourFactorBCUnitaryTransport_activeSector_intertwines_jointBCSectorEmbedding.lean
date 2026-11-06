-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_activeSector_intertwines_jointBCSectorEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:05:04.413081+00:00
-- url     : https://prove2.me/submissions/5353aecd-ae8d-4a54-bc0b-de8efd4881ad

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding


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
    {A B C D WB NB WC NC : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    [NormedAddCommGroup WC] [InnerProductSpace Complex WC] [Semantics.FiniteQuantumSystem WC]
    [NormedAddCommGroup NC] [InnerProductSpace Complex NC] [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (fourFactorBCUnitaryTransport (A := A) (D := D)
      (activeSectorPhysicalUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap.comp
        (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC) =
      (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC).comp
        (jointBCSectorActiveUnitary (A := A) pB pC
          (activeSectorJointBCUnitary pB pC UB UC U)).toLinearEquiv.toLinearMap := by
  exact fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
    (A := A) (D := D) pB pC (activeSectorPhysicalUnitary pB pC UB UC U)
    (activeSectorJointBCUnitary pB pC UB UC U)
    (activeSectorPhysicalUnitary_intertwines_submoduleTensorEmbedding pB pC UB UC U)
end QEC.Bounds.BPTCommutingProjectorModel
