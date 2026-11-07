-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:42:55.986812+00:00
-- url     : https://prove2.me/submissions/dee2549e-bf42-44db-ab8e-f9d92d7929e3

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator

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
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
        ((M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).conjOperator
          M.fullCodeProjector) =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator
          ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) := by
  exact M.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
    region pB pC UB UC U M.fullCodeProjector
end QEC.Bounds.BPTCommutingProjectorModel
