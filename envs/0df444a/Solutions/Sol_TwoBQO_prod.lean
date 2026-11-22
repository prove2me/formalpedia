-- Prove2me | solution 1 for TwoBQO.prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:50.532079+00:00
-- url     : https://prove2.me/submissions/18241b5d-bbec-442a-863e-831db107c376

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
public import Theorems.Thm_PairSeq_perfect_or_bad
public import Theorems.Thm_TwoBQO_iff_noBad

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace TwoBQO
theorem _root_.solution {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (hr : TwoBQO r)
    (hs : TwoBQO s) : TwoBQO fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2 := by
  rw [TwoBQO.iff_noBad] at hr hs ⊢
  intro ⟨f, hbad⟩
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  obtain ⟨e₁, he₁, hperf₁ | hbad₁⟩ := PairSeq.perfect_or_bad r f₁
  · let f₂ : PairSeq β := fun m n h => (PairSeq.restrict f e₁ he₁ m n h).2
    obtain ⟨e₂, he₂, hperf₂ | hbad₂⟩ := PairSeq.perfect_or_bad s f₂
    · -- Both coordinates are perfect along `e₁ ∘ e₂`, contradicting `hbad`.
      exact hbad (e₁ (e₂ 0)) (e₁ (e₂ 1)) (e₁ (e₂ 2))
        (he₁ (he₂ (by norm_num : 0 < 1))) (he₁ (he₂ (by norm_num : 1 < 2)))
        ⟨hperf₁ (e₂ 0) (e₂ 1) (e₂ 2) (he₂ (by norm_num : 0 < 1)) (he₂ (by norm_num : 1 < 2)),
         hperf₂ 0 1 2 (by norm_num : 0 < 1) (by norm_num : 1 < 2)⟩
    · exact hs ⟨PairSeq.restrict f₂ e₂ he₂, hbad₂⟩
  · exact hr ⟨PairSeq.restrict f₁ e₁ he₁, hbad₁⟩
end TwoBQO
