-- Prove2me | solution 1 for TwoBQO.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:06.691293+00:00
-- url     : https://prove2.me/submissions/bf80fbb5-28c0-488b-a4f4-77b845abcc34

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
public import Theorems.Thm_TwoBQO_iff_noBad

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α : Type*} {r s : α → α → Prop} (h : TwoBQO r)
    (hincl : ∀ a b, r a b → s a b) : TwoBQO s := by
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨f, fun m n l hmn hnl hrel => hbad m n l hmn hnl (hincl _ _ hrel)⟩
end TwoBQO
