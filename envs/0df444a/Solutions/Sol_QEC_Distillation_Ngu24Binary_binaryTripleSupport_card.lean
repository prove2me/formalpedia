-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTripleSupport_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:23:44.727479+00:00
-- url     : https://prove2.me/submissions/ee0f56f3-81d4-4adf-93d0-3ef2a2676d7c

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (x : J × Fin 512) :
    (binaryTripleSupport J x).card = 3 := by
  rw [binaryTripleSupport, Finset.card_map, Finset.card_univ]
  rfl
end QEC.Distillation.Ngu24Binary
