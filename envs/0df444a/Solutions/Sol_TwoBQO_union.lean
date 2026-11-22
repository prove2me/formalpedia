-- Prove2me | solution 1 for TwoBQO.union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:15.000186+00:00
-- url     : https://prove2.me/submissions/b07d5b25-51a3-40fb-a621-5b012f17c7d0

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
theorem _root_.solution {α : Type*} (r : α → α → Prop) (p q : α → Prop) (hcover : ∀ a, p a ∨ q a)
    (hp : TwoBQO (fun a b : {x : α // p x} => r a.val b.val))
    (hq : TwoBQO (fun a b : {x : α // q x} => r a.val b.val)) :
    TwoBQO r := by
  classical
  intro f
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_pairs fun m n h => (decide (p (f m n h)) : Bool)
  cases k with
  | true =>
    have hpf : ∀ i j (h : i < j), p (f (e i) (e j) (he h)) :=
      fun i j h => of_decide_eq_true (hk i j h)
    obtain ⟨i, j, l, hij, hjl, hrel⟩ := hp fun i j h => ⟨f (e i) (e j) (he h), hpf i j h⟩
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩
  | false =>
    have hqf : ∀ i j (h : i < j), q (f (e i) (e j) (he h)) :=
      fun i j h => (hcover _).resolve_left (of_decide_eq_false (hk i j h))
    obtain ⟨i, j, l, hij, hjl, hrel⟩ := hq fun i j h => ⟨f (e i) (e j) (he h), hqf i j h⟩
    exact ⟨e i, e j, e l, he hij, he hjl, hrel⟩
end TwoBQO
