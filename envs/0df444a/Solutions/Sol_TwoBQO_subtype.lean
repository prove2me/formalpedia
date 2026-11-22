-- Prove2me | solution 1 for TwoBQO.subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:49.750775+00:00
-- url     : https://prove2.me/submissions/f399737b-626f-4b0a-b455-a388becb0f87

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
public import Theorems.Thm_TwoBQO_comap

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α : Type*} {r : α → α → Prop} (h : TwoBQO r) (p : α → Prop) :
    TwoBQO fun a b : Subtype p => r a.val b.val :=
  h.comap Subtype.val
end TwoBQO
