-- Prove2me | solution 1 for WellQuasiOrdered.exists_monotone_subseq_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:40.133244+00:00
-- url     : https://prove2.me/submissions/67cfff56-74f4-486b-93b0-3cdca7dd3f5e

module
public import Mathlib.Order.WellQuasiOrder
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Basic
public import Theorems.Thm_Sequences_perfect_or_bad

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open Sequences
variable {α : Type*} {r : α → α → Prop}
namespace WellQuasiOrdered
theorem _root_.solution (h : WellQuasiOrdered r) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ m n : ℕ, m < n → r (f (e m)) (f (e n)) := by
  obtain ⟨e, he, hperf | hbad⟩ := perfect_or_bad r f
  · exact ⟨e, he, fun m n hmn => hperf m n hmn⟩
  · obtain ⟨m, n, hmn, hr⟩ := h (f ∘ e)
    exact absurd hr (hbad m n hmn)
end WellQuasiOrdered
