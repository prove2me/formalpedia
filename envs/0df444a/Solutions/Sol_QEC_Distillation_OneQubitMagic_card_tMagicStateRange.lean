-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.card_tMagicStateRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:17:42.83108+00:00
-- url     : https://prove2.me/submissions/c4184782-1e4f-4351-830d-a4e716a333f7

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tMagicState_injective
import Theorems.Thm_QEC_Distillation_OneQubitMagic_card_tDirection


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : (Set.range tMagicStateOfDirection).ncard = 8 := by
  rw [Set.ncard_range_of_injective tMagicState_injective,
    Nat.card_eq_fintype_card, card_tDirection]
end QEC.Distillation.OneQubitMagic
