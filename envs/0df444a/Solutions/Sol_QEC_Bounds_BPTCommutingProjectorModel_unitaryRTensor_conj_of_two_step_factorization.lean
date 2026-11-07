-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_of_two_step_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:53.377562+00:00
-- url     : https://prove2.me/submissions/f3e7f976-4c30-488d-884f-a91fa0adc5d7

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Bounds.BPTCommutingProjectorModel
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (U : Semantics.UnitaryTransport
      (Semantics.CompositeSystem N C) (Semantics.CompositeSystem N C))
    (Q : Semantics.Operator (Semantics.CompositeSystem (Semantics.CompositeSystem N C) D))
    (Theta A B : Semantics.Operator (Semantics.CompositeSystem N C))
    (P : Semantics.Operator D)
    (hfactor : Q = TensorProduct.map Theta P)
    (hTheta : Theta = A)
    (hconj : U.conjOperator A = B) :
    (unitaryRTensor U D).conjOperator Q = TensorProduct.map B P := by
  calc
    (unitaryRTensor U D).conjOperator Q =
        (unitaryRTensor U D).conjOperator (TensorProduct.map Theta P) := by
      rw [hfactor]
    _ = TensorProduct.map (U.conjOperator Theta) P :=
      unitaryRTensor_conj_tensorMap U Theta P
    _ = TensorProduct.map (U.conjOperator A) P := by
      rw [hTheta]
    _ = TensorProduct.map B P := by
      rw [hconj]
end QEC.Bounds.BPTCommutingProjectorModel
