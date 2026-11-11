-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:31:05.902144+00:00
-- url     : https://prove2.me/submissions/36e98a0e-99fc-4865-b2a6-8295a889365e

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
    phaseTransport.conjOperator (1 : Operator QubitSpace) = 1 :=
  UnitaryTransport.conjOperator_one phaseTransport
end QEC.Distillation.OneQubitMagic
