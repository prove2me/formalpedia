-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.nextIn_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:36.477997+00:00
-- url     : https://prove2.me/submissions/cc19e6fd-b196-4fcd-8151-94ba2297f51b

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
theorem _root_.solution {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : nextIn 𝒜 x ∈ 𝒜 := by
  rw [nextIn, dif_pos h]; exact (wo.wo.wf.min_mem _ h).1
end OrdinalStepUp.ErdosRado
