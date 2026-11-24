-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.disc_eq_of_disc_lt_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:30.52918+00:00
-- url     : https://prove2.me/submissions/e2d47657-f72e-49ce-b1ef-4505c6a6b4b6

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
theorem _root_.solution (hab : a ≠ b) (h : disc a b < disc b c) : disc a c = disc a b := by
  have hagree α (hα : α < disc a b) : (α ∈ a ↔ α ∈ c) :=
    (mem_iff_of_lt_disc hα).trans (mem_iff_of_lt_disc (hα.trans h))
  have hbc : disc a b ∈ b ↔ disc a b ∈ c := mem_iff_of_lt_disc h
  rcases disc_mem_symmDiff hab with hd | hd
  · rw [disc_comm]
    exact disc_eq_of_agree_before_and_differ_at (hagree · · |>.symm) (hbc.2 · |> hd.2) hd.1
  · exact disc_eq_of_agree_before_and_differ_at hagree hd.2 (hbc.1 hd.1)
end OrdinalStepUp.ErdosRado
