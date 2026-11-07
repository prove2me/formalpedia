-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_scalar_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:11:27.634047+00:00
-- url     : https://prove2.me/submissions/d20e7b57-bff2-493d-9c40-3aaffdcf2a30

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (Q R : Semantics.Operator H)
    (scalar : Complex) (hscalar : Q * R * Q = scalar • Q) :
    U.conjOperator Q * U.conjOperator R * U.conjOperator Q =
      scalar • U.conjOperator Q := by
  calc
    U.conjOperator Q * U.conjOperator R * U.conjOperator Q =
        U.conjOperator (Q * R * Q) := by
          rw [Semantics.UnitaryTransport.conjOperator_mul,
            Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.conjOperator (scalar • Q) := congrArg U.conjOperator hscalar
    _ = scalar • U.conjOperator Q := U.conjOperatorLinearMap.map_smul scalar Q
end QEC.Bounds.BPTCommutingProjectorModel
