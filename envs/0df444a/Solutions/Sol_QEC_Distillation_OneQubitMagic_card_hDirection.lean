-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.card_hDirection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:49:34.127983+00:00
-- url     : https://prove2.me/submissions/a5d53a46-90a0-4a94-8b70-b82ad5b13721

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : Fintype.card HDirection = 12 := by
  decide +kernel
end QEC.Distillation.OneQubitMagic
