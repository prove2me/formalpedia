-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commute_of_conjOperator_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:20:18.982171+00:00
-- url     : https://prove2.me/submissions/54c4a1e2-14e9-4588-8dda-d29ff70ff13c

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor

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
    (U : Semantics.UnitaryTransport H K)
    {P Q : Semantics.Operator H}
    (h : Commute (U.conjOperator P) (U.conjOperator Q)) :
    Commute P Q := by
  calc
    P * Q = U.symm.conjOperator (U.conjOperator (P * Q)) :=
      (U.symm_conjOperator_conjOperator (P * Q)).symm
    _ = U.symm.conjOperator (U.conjOperator P * U.conjOperator Q) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.symm.conjOperator (U.conjOperator Q * U.conjOperator P) :=
      congrArg U.symm.conjOperator h.eq
    _ = U.symm.conjOperator (U.conjOperator (Q * P)) := by
      exact congrArg U.symm.conjOperator
        (Semantics.UnitaryTransport.conjOperator_mul U Q P).symm
    _ = Q * P := U.symm_conjOperator_conjOperator (Q * P)
end QEC.Bounds.BPTCommutingProjectorModel
