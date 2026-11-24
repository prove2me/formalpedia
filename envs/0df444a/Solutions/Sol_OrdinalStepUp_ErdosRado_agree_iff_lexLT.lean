-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.agree_iff_lexLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:37.788245+00:00
-- url     : https://prove2.me/submissions/3daad0ff-3508-4c55-b61f-199523cc8e37

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
theorem _root_.solution (hab : a ≺w b) : Agree a b ↔ a ≺ b := by simp_all [Agree]
end OrdinalStepUp.ErdosRado
