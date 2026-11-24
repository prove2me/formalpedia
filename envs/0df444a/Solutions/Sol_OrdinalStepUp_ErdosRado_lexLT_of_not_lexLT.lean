-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.lexLT_of_not_lexLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:31.306831+00:00
-- url     : https://prove2.me/submissions/3b234a2a-774d-410b-a46d-7e98c908778a

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
theorem _root_.solution (hab : a ≺w b) (h : ¬ a ≺ b) : b ≺ a := by
  by_contra
  have e : a = b := by grind [trichotomous_of LexLT a b]
  exact irrefl b (e ▸ hab)
end OrdinalStepUp.ErdosRado
