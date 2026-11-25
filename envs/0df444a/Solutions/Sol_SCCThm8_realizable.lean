-- Prove2me | solution 1 for SCCThm8.realizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:59:16.548454+00:00
-- url     : https://prove2.me/submissions/9878cf19-9696-4758-8342-12a58310c6aa

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_realize_aux

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution (k : ℕ) (m : Fin (3 * k) → ℤ) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 3)
    (hs : ∑ i, m i = 3 * k) :
    ∃ A B C : Finset (Fin (3 * k)), A.card = k ∧ B.card = k ∧ C.card = k ∧
      ∀ i, mult A B C i = m i := by
  obtain ⟨A, B, C, -, -, -, cA, cB, cC, hmul⟩ :=
    realize_aux (fun i => (m i).toNat) (fun i => by have := hm i; omega) univ
  have hsum : ∑ i, (m i).toNat = 3 * k := by
    have : ((∑ i, (m i).toNat : ℕ) : ℤ) = 3 * k := by
      rw [Nat.cast_sum, ← hs]
      exact sum_congr rfl fun i _ => by have := hm i; omega
    exact_mod_cast this
  rw [hsum] at cA cB cC
  refine ⟨A, B, C, by omega, by omega, by omega, fun i => ?_⟩
  have h1 := hmul i (mem_univ i)
  have h2 := hm i
  unfold mult
  split_ifs at h1 ⊢ <;> simp at h1 <;> omega
end SCCThm8
