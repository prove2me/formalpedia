-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.conjOperator_eq_symm_conjOperator_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:07:42.261345+00:00
-- url     : https://prove2.me/submissions/b6e91f4a-2b15-462c-8276-8707b8e0b5fc

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportBasic

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
    (T : Semantics.UnitaryTransport H K)
    (W : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (C : Semantics.Operator H) (P Q : Semantics.Operator K)
    (htransport : T.conjOperator (W.conjOperator C) =
      V.conjOperator (T.conjOperator C))
    (hproduct : V.conjOperator (T.conjOperator C) = P)
    (hbefore : P = Q) :
    W.conjOperator C = T.symm.conjOperator Q := by
  calc
    W.conjOperator C = T.symm.conjOperator (T.conjOperator (W.conjOperator C)) :=
      (T.symm_conjOperator_conjOperator _).symm
    _ = T.symm.conjOperator (V.conjOperator (T.conjOperator C)) :=
      congrArg T.symm.conjOperator htransport
    _ = T.symm.conjOperator P := congrArg T.symm.conjOperator hproduct
    _ = T.symm.conjOperator Q := congrArg T.symm.conjOperator hbefore
end QEC.Bounds.BPTCommutingProjectorModel
