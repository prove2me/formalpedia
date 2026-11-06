-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetric_conjOperator_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:19:43.518819+00:00
-- url     : https://prove2.me/submissions/d5da9829-d835-43bf-812c-fc4a6441d868

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
    (U : Semantics.UnitaryTransport H K) (P : Semantics.Operator H) :
    (U.conjOperator P).IsSymmetric ↔ P.IsSymmetric := by
  constructor
  · intro h
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint P).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    have hTransportSelf : LinearMap.adjoint (U.conjOperator P) = U.conjOperator P :=
      LinearMap.isSelfAdjoint_iff'.mp
        ((LinearMap.isSymmetric_iff_isSelfAdjoint (U.conjOperator P)).mp h)
    calc
      LinearMap.adjoint P =
          U.symm.conjOperator (U.conjOperator (LinearMap.adjoint P)) :=
        (Semantics.UnitaryTransport.symm_conjOperator_conjOperator U
          (LinearMap.adjoint P)).symm
      _ = U.symm.conjOperator (LinearMap.adjoint (U.conjOperator P)) :=
        congrArg U.symm.conjOperator
          (Semantics.UnitaryTransport.conjOperator_adjoint U P).symm
      _ = U.symm.conjOperator (U.conjOperator P) :=
        congrArg U.symm.conjOperator hTransportSelf
      _ = P := Semantics.UnitaryTransport.symm_conjOperator_conjOperator U P
  · intro h
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint (U.conjOperator P)).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    calc
      LinearMap.adjoint (U.conjOperator P) = U.conjOperator (LinearMap.adjoint P) :=
        Semantics.UnitaryTransport.conjOperator_adjoint U P
      _ = U.conjOperator P := congrArg U.conjOperator
        (LinearMap.isSelfAdjoint_iff'.mp
          ((LinearMap.isSymmetric_iff_isSelfAdjoint P).mp h))
end QEC.Bounds.BPTCommutingProjectorModel
