-- Prove2me | solution 1 for QEC.Bounds.registerFactorizedTensor_compression_left_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:29.493173+00:00
-- url     : https://prove2.me/submissions/0fe868bb-04ba-4ef4-9835-aa56e24e825d

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorBridge
import Theorems.Thm_QEC_Bounds_registerFactorizedTensor_compression_left


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
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
    (J : Semantics.CompositeSystem H K →ₗ[Complex] S.factorizedSystem)
    (hJ : J = TensorProduct.map eSel eComp)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint J).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp J) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by
  rw [hJ]
  exact registerFactorizedTensor_compression_left q S eSel eComp hComp A
end QEC.Bounds
