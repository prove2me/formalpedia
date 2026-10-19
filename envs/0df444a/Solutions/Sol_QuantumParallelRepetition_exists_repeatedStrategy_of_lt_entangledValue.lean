-- Prove2me | solution 1 for QuantumParallelRepetition.exists_repeatedStrategy_of_lt_entangledValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/25cf14ec-6454-4fe7-b27a-e332b95a1cd2

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n), r < S.winProbability := by
  let values : Set ℝ :=
    Set.range (Strategy.winProbability (G := G.repeat n))
  have hnonempty : values.Nonempty := by
    by_contra hempty
    have heq : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : repeatedEntangledValue G n = 0 := by
      change sSup values = 0
      rw [heq, Real.sSup_empty]
    linarith
  have hs : r < sSup values := by
    exact hvalue
  obtain ⟨v, ⟨S, hS⟩, hv⟩ := exists_lt_of_lt_csSup hnonempty hs
  subst v
  exact ⟨S, hv⟩
end QuantumParallelRepetition
