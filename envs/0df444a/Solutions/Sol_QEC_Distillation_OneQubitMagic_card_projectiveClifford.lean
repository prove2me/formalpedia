-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.card_projectiveClifford
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:14:35.673608+00:00
-- url     : https://prove2.me/submissions/d4f480f5-aa15-49b2-ab9e-28412f58ff7b

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : Fintype.card ProjectiveClifford = 24 := by
  decide +kernel
end QEC.Distillation.OneQubitMagic
