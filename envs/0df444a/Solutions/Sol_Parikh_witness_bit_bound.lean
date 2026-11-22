-- Prove2me | solution 1 for Parikh.witness_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:05.915247+00:00
-- url     : https://prove2.me/submissions/ccbdfd51-dd8c-4d55-93c3-73da0873cc51

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Fintype T] (s : GrammarSize)
    (hd : s.terminals = Fintype.card T) (W : Witness T) (h : WithinBounds s W) :
    entryBits s W ≤ s.vectorBits ∧
      (∀ c ∈ W, ∀ a, c.base a < 2 ^ s.coordinateBits) ∧
      (∀ c ∈ W, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ s.coordinateBits) := by
  classical
  have hwidth : (s.trees + 1) * s.positions < 2 ^ s.coordinateBits := by
    apply lt_of_lt_of_le (Nat.lt_succ_self _)
    exact (Nat.le_pow_clog (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  have hcoordinate (v : Vector T) (a : T) : v a ≤ norm v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hpositions : s.positions ≤ (s.trees + 1) * s.positions := by
    simpa using Nat.mul_le_mul_right s.positions (Nat.le_add_left 1 s.trees)
  refine ⟨?_, ?_, ?_⟩
  · have hentries : entryBits s W ≤
        W.length * ((s.trees + 1) * s.terminals * s.coordinateBits) := by
      unfold entryBits
      have bound : ∀ (l : List ℕ) (B : ℕ), (∀ n ∈ l, n ≤ B) → l.sum ≤ l.length * B := by
        intro l B
        induction l with
        | nil => simp
        | cons a l ih =>
          intro hl
          have ha := hl a (by simp)
          have ht := ih (fun n hn => hl n (by simp [hn]))
          simp only [List.sum_cons, List.length_cons]
          rw [Nat.add_mul, one_mul]
          omega
      have hsum := bound
        (W.map fun c => (c.periods.length + 1) * Fintype.card T * s.coordinateBits)
        ((s.trees + 1) * s.terminals * s.coordinateBits) (by
          intro n hn
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
          rw [← hd]
          exact Nat.mul_le_mul_right _
            (Nat.mul_le_mul_right _ (Nat.add_le_add_right (h.2 c hc).1 1)))
      simpa only [List.length_map, Nat.nsmul_eq_mul] using hsum
    exact hentries.trans (by
      simpa only [GrammarSize.vectorBits, Nat.mul_assoc] using
        Nat.mul_le_mul_right ((s.trees + 1) * s.terminals * s.coordinateBits) h.1)
  · intro c hc a
    exact lt_of_le_of_lt ((hcoordinate c.base a).trans (h.2 c hc).2.1) hwidth
  · intro c hc p hp a
    exact lt_of_le_of_lt
      ((hcoordinate p a).trans (((h.2 c hc).2.2 p hp).trans hpositions)) hwidth
end Parikh
