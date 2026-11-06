-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_conjOperator_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:21:32.326095+00:00
-- url     : https://prove2.me/submissions/e06ccfce-4140-49f3-978f-5cb1efabe9ba

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetric_conjOperator_iff

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
    (U : Semantics.UnitaryTransport H K) (P : Semantics.Operator H) :
    (U.conjOperator P).IsSymmetricProjection ↔ P.IsSymmetricProjection := by
  constructor
  · intro h
    constructor
    · calc
        P * P = U.symm.conjOperator (U.conjOperator (P * P)) :=
          (U.symm_conjOperator_conjOperator (P * P)).symm
        _ = U.symm.conjOperator (U.conjOperator P * U.conjOperator P) := by
          rw [Semantics.UnitaryTransport.conjOperator_mul]
        _ = U.symm.conjOperator (U.conjOperator P) :=
          congrArg U.symm.conjOperator h.isIdempotentElem
        _ = P := U.symm_conjOperator_conjOperator P
    · exact (isSymmetric_conjOperator_iff U P).mp h.isSymmetric
  · intro h
    constructor
    · calc
        U.conjOperator P * U.conjOperator P = U.conjOperator (P * P) :=
          (Semantics.UnitaryTransport.conjOperator_mul U P P).symm
        _ = U.conjOperator P := congrArg U.conjOperator h.isIdempotentElem
    · exact (isSymmetric_conjOperator_iff U P).mpr h.isSymmetric
end QEC.Bounds.BPTCommutingProjectorModel
