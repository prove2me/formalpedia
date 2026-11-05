-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.predecessor_in_scope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:35.76503+00:00
-- url     : https://prove2.me/submissions/55979d05-aa1a-41eb-8d1f-cddd7e1eb4e6

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
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_predecessor_below

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N c T ∨
      predecessor R i ∈ near c Q (cost c Q - (T + 1)) :=
  below_bank_or_near hc (fun j => (predecessor_below R i j).trans (hRQ j))
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
