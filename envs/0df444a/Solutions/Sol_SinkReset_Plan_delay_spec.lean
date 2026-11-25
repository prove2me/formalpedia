-- Prove2me | solution 1 for SinkReset.Plan.delay_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:42.361164+00:00
-- url     : https://prove2.me/submissions/d823ff4c-b202-4853-b7ea-7e3d7bd8190b

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) :
    delay k m S ≤ m ∧
    ((active S).Nonempty → ∃ q ∈ active S, cycleDelta k m q = delay k m S) ∧
    (∀ q ∈ active S, delay k m S ≤ cycleDelta k m q) := by
  have hδm : ∀ q, cycleDelta k m q ≤ m := fun q => by
    have := q.isLt
    unfold cycleDelta; split_ifs <;> omega
  unfold delay
  refine ⟨?_, ?_, ?_⟩
  · rcases (active S).eq_empty_or_nonempty with h | ⟨q, hq⟩
    · have : {r | ∃ q ∈ active S, cycleDelta k m q = r} = ∅ := by
        ext r; simp [h]
      rw [this, Nat.sInf_empty]; omega
    · exact (Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)).trans (hδm _)
  · rintro ⟨q, hq⟩
    have := Nat.sInf_mem (s := {r | ∃ q ∈ active S, cycleDelta k m q = r}) ⟨_, q, hq, rfl⟩
    rw [Set.mem_setOf_eq] at this
    exact this
  · intro q hq
    exact Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)
end SinkReset.Plan
