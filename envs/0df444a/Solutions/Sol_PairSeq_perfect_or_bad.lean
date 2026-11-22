-- Prove2me | solution 1 for PairSeq.perfect_or_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:12.753701+00:00
-- url     : https://prove2.me/submissions/6addaf57-fabe-440c-affd-7a71cb65f733

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
public import Theorems.Thm_infinite_ramsey_triples


set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
open PairSeq
namespace PairSeq
theorem _root_.solution {α : Type*} (r : α → α → Prop) (f : PairSeq α) :
    ∃ (e : ℕ → ℕ) (he_mono : StrictMono e),
      IsPerfect r (restrict f e he_mono) ∨ IsBad r (restrict f e he_mono) := by
  classical
  obtain ⟨e, he_mono, k, hk⟩ := @infinite_ramsey_triples Bool inferInstance
    fun h i j (hs : h < i ∧ i < j) => decide (r (f h i hs.1) (f i j hs.2))
  refine ⟨e, he_mono, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hk_false | hk_true
  · left
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_false] at h_color
    simpa [restrict, decide_eq_false_iff_not] using h_color
  · right
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_true] at h_color
    simpa [restrict, decide_eq_true_eq] using h_color
end PairSeq
