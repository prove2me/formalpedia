-- Prove2me | solution 1 for card_valid_bases_sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:44:33.780992+00:00
-- url     : https://prove2.me/submissions/46f4dafb-5205-49b7-9f5c-8137181b95de

import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Sum
import Definitions.Def_CARDB

set_option autoImplicit true
open Set TopologicalSpace
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (t : TopologicalSpace α)
omit [DecidableEq α]
theorem _root_.solution :
    Fintype.card (ValidBasis α) =
      ∑ τ : TopologicalSpace α, Fintype.card (Fiber τ) := by
  rw [← Fintype.card_congr
    (Equiv.sigmaFiberEquiv (fun B : ValidBasis α => generateFrom B.1))]
  rw [Fintype.card_sigma]
