-- Prove2me | solution 1 for TwoBQO.wellQuasiOrdered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:36.889406+00:00
-- url     : https://prove2.me/submissions/f06913a5-9278-49b3-8ca1-a19912545743

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

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α : Type*} {r : α → α → Prop} (h : TwoBQO r) :
    WellQuasiOrdered r := fun g =>
  let ⟨m, n, _, hmn, _, hrel⟩ := h fun m _ _ => g m
  ⟨m, n, hmn, hrel⟩
end TwoBQO
