-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tDirection_transitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:14:44.076718+00:00
-- url     : https://prove2.me/submissions/4f24c556-bd20-44a5-9cb9-467c57b0e089

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (a b : TDirection) :
    ∃ g : ProjectiveClifford, g • a = b := by
  revert a b
  decide +kernel
end QEC.Distillation.OneQubitMagic
