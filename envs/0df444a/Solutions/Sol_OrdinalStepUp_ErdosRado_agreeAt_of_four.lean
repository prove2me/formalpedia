-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.agreeAt_of_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:15.430683+00:00
-- url     : https://prove2.me/submissions/c1ee0cc3-d65a-4b25-a5f7-d99cdad00d84

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {u : FinChain (n + 4)}
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) :
    (AgreeAt u 0 ↔ a ≺ b) ∧ (AgreeAt u 1 ↔ b ≺ c) := by
  constructor
  · rw [AgreeAt, show ((0 : Fin (n + 3)).castSucc) = (0 : Fin (n + 4)) from by first | rfl,
      show ((0 : Fin (n + 3)).succ) = (1 : Fin (n + 4)) from by first | rfl, h0, h1]
  · rw [AgreeAt, show ((1 : Fin (n + 3)).castSucc) = (1 : Fin (n + 4)) from by first | rfl,
      show ((1 : Fin (n + 3)).succ) = (2 : Fin (n + 4)) from by first | rfl, h1, h2]
end OrdinalStepUp.ErdosRado
