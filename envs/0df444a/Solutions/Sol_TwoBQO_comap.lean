-- Prove2me | solution 1 for TwoBQO.comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:05.775364+00:00
-- url     : https://prove2.me/submissions/50eca0f6-6ae5-432e-bcd3-48fac0604f7d

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
theorem _root_.solution {α β : Type*} {r : α → α → Prop} (h : TwoBQO r) (φ : β → α) :
    TwoBQO fun a b => r (φ a) (φ b) := by
  rw [TwoBQO.iff_noBad] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨fun m n hmn => φ (f m n hmn), fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel⟩
end TwoBQO
