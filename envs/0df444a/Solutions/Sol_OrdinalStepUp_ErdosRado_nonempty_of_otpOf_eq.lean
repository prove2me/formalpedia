-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.nonempty_of_otpOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:00.445812+00:00
-- url     : https://prove2.me/submissions/5da2af9e-d6b1-4637-9d52-d2448ea8c5bb

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_IsIndec_ne_zero

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) : 𝒜.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro rfl
  exact hA.ne_zero (show otpOf _ ∅ = 0 by simp [otpOf])
end OrdinalStepUp.ErdosRado
