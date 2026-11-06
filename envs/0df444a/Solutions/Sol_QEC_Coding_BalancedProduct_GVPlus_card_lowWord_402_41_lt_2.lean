-- Prove2me | solution 2 for QEC.Coding.BalancedProduct.GVPlus.card_lowWord_402_41_lt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:02:37.759183+00:00
-- url     : https://prove2.me/submissions/4dec19f1-fbde-4d85-8c66-37cd9bde4ac0

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.BalancedProduct.GVPlus
open Classical

theorem solution :
    Fintype.card (LowWord 402 41) < 2 ^ 185 := by
  rw [card_lowWordOn, Fintype.card_fin]
  decide +kernel
