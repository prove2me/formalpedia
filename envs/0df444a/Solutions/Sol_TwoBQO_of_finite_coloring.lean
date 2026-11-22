-- Prove2me | solution 1 for TwoBQO.of_finite_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:14.049032+00:00
-- url     : https://prove2.me/submissions/bdba7b09-e4ed-45b5-ae98-097f41f057b7

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
public import Theorems.Thm_infinite_ramsey_pairs


set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α κ : Type*} [Finite κ] (r : α → α → Prop) (c : α → κ)
    (hc : ∀ a b, c a = c b → r a b) : TwoBQO r := by
  intro f
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_pairs fun m n h => c (f m n h)
  exact ⟨e 0, e 1, e 2, he (by norm_num), he (by norm_num),
    hc _ _ ((hk 0 1 (by norm_num)).trans (hk 1 2 (by norm_num)).symm)⟩
end TwoBQO
