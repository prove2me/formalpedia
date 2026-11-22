-- Prove2me | solution 1 for TwoBQO.lexSigmaQO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:27.031743+00:00
-- url     : https://prove2.me/submissions/7d5b2a83-e059-4f52-b8bf-f10eed2808e0

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
public import Theorems.Thm_TwoBQO_lexSigmaQO_reflect

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
namespace TwoBQO
theorem _root_.solution {ι : Type*} (r : ι → ι → Prop) (hr : TwoBQO r) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) (ht : ∀ i, TwoBQO (t i)) : TwoBQO (TwoBQO.LexSumRelQO r s t) := by
  rw [TwoBQO.iff_noBad]
  rintro ⟨f, hf⟩
  obtain ⟨e, he, hbad | ⟨i, hmem, hbad⟩⟩ := TwoBQO.lexSigmaQO_reflect r s t f hf
  · exact (TwoBQO.iff_noBad r).mp hr ⟨_, hbad⟩
  · exact (TwoBQO.iff_noBad (t i)).mp (ht i) ⟨_, hbad⟩
end TwoBQO
