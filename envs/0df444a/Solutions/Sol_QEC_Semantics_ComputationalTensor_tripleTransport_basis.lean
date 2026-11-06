-- Prove2me | solution 1 for QEC.Semantics.ComputationalTensor.tripleTransport_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:02:44.184536+00:00
-- url     : https://prove2.me/submissions/89507952-d6f5-401f-9428-2b78f3810560

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalTensor
open scoped TensorProduct
variable (A B : Type) [Fintype A] [Fintype B]
namespace QEC.Semantics.ComputationalTensor
theorem _root_.solution (a : A × A × A) :
    tripleTransport A (tripleBasis A a) = EuclideanSpace.basisFun _ Complex a :=
  OrthonormalBasis.equiv_apply_basis _ _ _ _
end QEC.Semantics.ComputationalTensor
