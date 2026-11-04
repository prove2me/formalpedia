-- Prove2me | solution 1 for WeightedCache.predecessor_in_scope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:43.970612+00:00
-- url     : https://prove2.me/submissions/0e7bad51-31b3-414f-bdb2-7e1d0cf5e92c

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
import Theorems.Thm_WeightedCache_predecessor_below

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N c T ∨
      predecessor R i ∈ near c Q (cost c Q - (T + 1)) :=
  below_bank_or_near hc (fun j => (predecessor_below R i j).trans (hRQ j))
end WeightedCache
