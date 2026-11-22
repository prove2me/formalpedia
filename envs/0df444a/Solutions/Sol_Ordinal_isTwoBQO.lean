-- Prove2me | solution 1 for Ordinal.isTwoBQO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:49.29266+00:00
-- url     : https://prove2.me/submissions/f944fbff-26f8-43fc-acca-924405500cfa

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Theorems.Thm_TwoBQO_of_wellFoundedLT

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace Ordinal
theorem _root_.solution : TwoBQO (α := Ordinal) (· ≤ ·) :=
  TwoBQO.of_wellFoundedLT
end Ordinal
