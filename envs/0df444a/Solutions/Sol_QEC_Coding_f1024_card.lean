-- Prove2me | solution 1 for QEC.Coding.f1024_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:17:20.846497+00:00
-- url     : https://prove2.me/submissions/9ede85b2-6705-4c1a-90cc-a2396c5b8065

import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Theorems.Thm_QEC_Coding_f1024_finrank

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Fintype.card F1024 = 1024 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F1024), ZMod.card 2, f1024_finrank]
  norm_num
end QEC.Coding
