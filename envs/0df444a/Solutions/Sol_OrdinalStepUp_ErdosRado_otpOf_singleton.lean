-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.otpOf_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:41.365832+00:00
-- url     : https://prove2.me/submissions/85fb53e4-d178-41ad-bcab-bcc955288bb7

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
theorem _root_.solution {v}: otpOf wo {v} = 1 := by simp [otpOf]
end OrdinalStepUp.ErdosRado
