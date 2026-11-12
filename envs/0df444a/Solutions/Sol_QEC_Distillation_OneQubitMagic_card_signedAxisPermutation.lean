-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.card_signedAxisPermutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:14:25.2082+00:00
-- url     : https://prove2.me/submissions/f31251a4-1d50-40c0-8f55-c9b3a555d966

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : Fintype.card SignedAxisPermutation = 48 := by
  decide +kernel
end QEC.Distillation.OneQubitMagic
