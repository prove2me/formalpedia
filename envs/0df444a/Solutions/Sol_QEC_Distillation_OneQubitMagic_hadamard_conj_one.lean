-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamard_conj_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:02.760773+00:00
-- url     : https://prove2.me/submissions/8b87a364-f46e-4914-b096-fd267fa2802d

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
noncomputable section
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    hadamardTransport.conjOperator (1 : Operator QubitSpace) = 1 :=
  UnitaryTransport.conjOperator_one hadamardTransport
end QEC.Distillation.OneQubitMagic
