-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.discSeq_of_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:09.838192+00:00
-- url     : https://prove2.me/submissions/dfa26be1-840a-4ed5-984d-f606609bcc36

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
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) (h3 : u 3 = e) :
    discSeq u 0 = disc a b ∧ discSeq u 1 = disc b c ∧ discSeq u 2 = disc c e := by
  refine ⟨?_, ?_, ?_⟩
  · rw [discSeq, show ((0 : Fin (n + 3)).castSucc) = (0 : Fin (n + 4)) from by first | rfl,
      show ((0 : Fin (n + 3)).succ) = (1 : Fin (n + 4)) from by first | rfl, h0, h1]
  · rw [discSeq, show ((1 : Fin (n + 3)).castSucc) = (1 : Fin (n + 4)) from by first | rfl,
      show ((1 : Fin (n + 3)).succ) = (2 : Fin (n + 4)) from by first | rfl, h1, h2]
  · rw [discSeq, show ((2 : Fin (n + 3)).castSucc) = (2 : Fin (n + 4)) from by first | rfl,
      show ((2 : Fin (n + 3)).succ) = (3 : Fin (n + 4)) from by first | rfl, h2, h3]
end OrdinalStepUp.ErdosRado
