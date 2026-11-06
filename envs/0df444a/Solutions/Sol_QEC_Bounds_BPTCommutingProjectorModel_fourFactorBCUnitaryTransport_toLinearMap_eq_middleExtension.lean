-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:34:30.190127+00:00
-- url     : https://prove2.me/submissions/56ec6ab6-7819-45ce-8b29-3331c21a9242

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport

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
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C)) :
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map E.toLinearEquiv.toLinearMap
            (1 : Semantics.Operator D))) := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
