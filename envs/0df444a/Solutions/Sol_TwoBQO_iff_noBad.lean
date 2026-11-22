-- Prove2me | solution 1 for TwoBQO.iff_noBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:35.719682+00:00
-- url     : https://prove2.me/submissions/25f82932-d73d-4cfc-a568-b5c570c6eac9

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
theorem _root_.solution {α : Type*} (r : α → α → Prop) : TwoBQO r ↔ TwoBQON r := by
  simp only [TwoBQON, PairSeq.IsBad, not_exists, not_forall, not_not]
  exact Iff.symm (Eq.to_iff rfl)
end TwoBQO
