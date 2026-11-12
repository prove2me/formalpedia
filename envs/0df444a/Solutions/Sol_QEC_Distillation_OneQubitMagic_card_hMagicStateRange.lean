-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.card_hMagicStateRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:17:57.088214+00:00
-- url     : https://prove2.me/submissions/050aa2b3-e045-4796-99e9-363e3f713edb

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hMagicState_injective
import Theorems.Thm_QEC_Distillation_OneQubitMagic_card_hDirection


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : (Set.range hMagicStateOfDirection).ncard = 12 := by
  rw [Set.ncard_range_of_injective hMagicState_injective,
    Nat.card_eq_fintype_card, card_hDirection]
end QEC.Distillation.OneQubitMagic
