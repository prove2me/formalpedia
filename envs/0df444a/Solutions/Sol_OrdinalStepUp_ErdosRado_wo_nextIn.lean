-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.wo_nextIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:37.127281+00:00
-- url     : https://prove2.me/submissions/8bf9a4f8-c9d2-4ab7-bfa6-06d9a0e09a5a

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
theorem _root_.solution {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : wo.r x (nextIn 𝒜 x) := by
  rw [nextIn, dif_pos h]; exact (wo.wo.wf.min_mem _ h).2
end OrdinalStepUp.ErdosRado
