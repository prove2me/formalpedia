-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hDirection_transitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:14:50.683714+00:00
-- url     : https://prove2.me/submissions/92ce06a7-c736-43bd-897c-95adf17530f6

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (a b : HDirection) :
    ∃ g : ProjectiveClifford, g • a = b := by
  revert a b
  decide +kernel
end QEC.Distillation.OneQubitMagic
