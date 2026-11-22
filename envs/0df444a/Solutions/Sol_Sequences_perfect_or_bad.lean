-- Prove2me | solution 1 for Sequences.perfect_or_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:13.235275+00:00
-- url     : https://prove2.me/submissions/52f7e68c-2970-4dba-b803-93587f5bbbe7

module
public import Mathlib.Order.WellQuasiOrder
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Basic
public import Theorems.Thm_infinite_ramsey_pairs


set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open Sequences
variable {α : Type*}
namespace Sequences
theorem _root_.solution (r : α → α → Prop) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ (IsPerfect r (f ∘ e) ∨ IsBad r (f ∘ e)) := by
  classical
  obtain ⟨e, he, k, hk⟩ := @infinite_ramsey_pairs Bool inferInstance
    (fun m n (_ : m < n) => decide (¬ r (f m) (f n)))
  refine ⟨e, he, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hktrue | hkfalse
  · -- colour `true`: `¬ r` on every pair — bad.
    right
    intro m n hmn
    have hc : ¬ r (f (e m)) (f (e n)) := of_decide_eq_true (hktrue ▸ hk m n hmn)
    simpa [Function.comp] using hc
  · -- colour `false`: `¬ ¬ r`, i.e. `r` holds on every pair — perfect.
    left
    intro m n hmn
    have hc : ¬ ¬ r (f (e m)) (f (e n)) := of_decide_eq_false (hkfalse ▸ hk m n hmn)
    simpa [Function.comp] using not_not.mp hc
end Sequences
