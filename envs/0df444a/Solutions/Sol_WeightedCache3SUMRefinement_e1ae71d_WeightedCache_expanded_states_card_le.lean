-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.expanded_states_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:36.363357+00:00
-- url     : https://prove2.me/submissions/9fb98ee3-ad9c-4e46-8d93-1eb9d586ad55

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
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_below_bank_or_near

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N T : ℕ} (c : Fin 3 → ℕ) (hc : Monotone c)
    (Q : Word N) (S : Finset (Word N))
    (hS : ∀ R ∈ S, Below R Q ∧ R ∉ bank N c T) :
    S.card ≤ (near c Q (cost c Q - (T + 1))).card := by
  apply card_le_card
  intro R hR
  obtain ⟨hb, hn⟩ := hS R hR
  exact (below_bank_or_near hc hb).resolve_left hn
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
