-- Prove2me | solution 1 for QEC.Locality.inner_ket_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:59.804749+00:00
-- url     : https://prove2.me/submissions/1458c845-b80d-4071-9758-2116004356b3

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    inner Complex (ket a) (ket b) = if a = b then 1 else 0 := by
  exact (EuclideanSpace.basisFun (Qubit.Bitstring α) Complex).inner_eq_ite a b
end QEC.Locality
