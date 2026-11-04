-- Prove2me | solution 1 for WeightedCache.expanded_states_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:30.659361+00:00
-- url     : https://prove2.me/submissions/3195b267-773b-4abb-9108-e35f5096760d

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache_below_bank_or_near

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N T : ℕ} (c : Fin 3 → ℕ) (hc : Monotone c)
    (Q : Word N) (S : Finset (Word N))
    (hS : ∀ R ∈ S, Below R Q ∧ R ∉ bank N c T) :
    S.card ≤ (near c Q (cost c Q - (T + 1))).card := by
  apply card_le_card
  intro R hR
  obtain ⟨hb, hn⟩ := hS R hR
  exact (below_bank_or_near hc hb).resolve_left hn
end WeightedCache
