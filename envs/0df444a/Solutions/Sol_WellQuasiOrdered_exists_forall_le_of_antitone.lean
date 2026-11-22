-- Prove2me | solution 1 for WellQuasiOrdered.exists_forall_le_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:54.717215+00:00
-- url     : https://prove2.me/submissions/4122cc2c-c5c1-4c43-a457-130aca3cf069

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace WellQuasiOrdered
theorem _root_.solution {β : Type*} {r : β → β → Prop}
    [IsPreorder β r] (hwqo : WellQuasiOrdered r) (a : ℕ → β)
    (hanti : ∀ m n : ℕ, m ≤ n → r (a n) (a m)) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → r (a m) (a n) := by
  by_contra h_contra
  obtain ⟨idx, hidx⟩ : ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ k, ¬ r (a (idx k)) (a (idx (k + 1))) := by
    have h_seq : ∀ k, ∃ n > k, ¬ r (a k) (a n) := fun k => by
      push Not at h_contra
      obtain ⟨n, hn₁, hn₂⟩ := h_contra k
      exact ⟨n, lt_of_le_of_ne hn₁ (by rintro rfl; exact hn₂ (refl_of r _)), hn₂⟩
    choose f hf using h_seq
    exact ⟨fun k => Nat.recOn k 0 fun k ih => f ih,
      strictMono_nat_of_lt_succ fun k => (hf _).1, fun k => (hf _).2⟩
  obtain ⟨k, l, hkl, h⟩ := hwqo fun n => a (idx n)
  exact hidx.2 k (trans_of r h (hanti _ _ (hidx.1.monotone (Nat.succ_le_of_lt hkl))))
end WellQuasiOrdered
