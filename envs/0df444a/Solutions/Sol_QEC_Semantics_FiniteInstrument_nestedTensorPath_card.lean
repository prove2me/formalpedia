-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorPath_card
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:54.716186+00:00
-- url     : https://prove2.me/submissions/5638c3ea-6c74-40d6-ac28-97f53f708c16

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem solution (branches depth : Nat) :
    Fintype.card (nestedTensorPath branches depth) = branches ^ depth := by
  rw [Fintype.card_congr (nestedTensorPathEquiv branches depth)]
  simp
