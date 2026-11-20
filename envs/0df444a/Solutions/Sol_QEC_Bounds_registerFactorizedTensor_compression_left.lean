-- Prove2me | solution 1 for QEC.Bounds.registerFactorizedTensor_compression_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:02.065462+00:00
-- url     : https://prove2.me/submissions/043261a7-c0f1-45c5-8a75-4d2dced5aff0

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_registerFactorization_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorEmbedding_compression_left


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 50000
namespace QEC.Bounds
theorem _root_.solution
    {iota : Type u} [Fintype iota] [DecidableEq iota] (q : iota → Nat)
    (S : Semantics.QuditSubsystem q)
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (eSel : H →ₗ[Complex] S.selectedSystem) (eComp : K →ₗ[Complex] S.complementSystem)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint (TensorProduct.map eSel eComp)).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp
          (TensorProduct.map eSel eComp)) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by
  rw [BPTCommutingProjectorModel.registerFactorization_conj_extendLocalToRegister]
  exact BPTCommutingProjectorModel.tensorEmbedding_compression_left eSel eComp hComp A
end QEC.Bounds
