-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:39.649341+00:00
-- url     : https://prove2.me/submissions/3de9a260-7808-4fab-813c-09e1acd29780

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_boundaryLocalUnitaryToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conj_conjugateUnitaryTransport_toLinearMap


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
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        (activeSectorPhysicalUnitary SB SC UB UC U).toLinearEquiv.toLinearMap := by
  unfold activeSectorBoundaryGlobalUnitary
  rw [M.fourFactorTransport_conj_boundaryLocalUnitaryToRegister]
  unfold activeSectorBoundaryUnitary
  exact congrArg (M.fourFactorExtendBC region)
    (conj_conjugateUnitaryTransport_toLinearMap
      (M.boundarySelectedToBCTransport region)
      (activeSectorPhysicalUnitary SB SC UB UC U))
end QEC.Bounds.BPTCommutingProjectorModel
