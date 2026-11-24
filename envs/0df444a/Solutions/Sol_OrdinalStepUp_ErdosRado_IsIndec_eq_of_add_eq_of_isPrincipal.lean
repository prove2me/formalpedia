-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.IsIndec.eq_of_add_eq_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:34.946062+00:00
-- url     : https://prove2.me/submissions/77a39174-b13f-4a50-aa11-0d29feb83ace

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
namespace IsIndec
theorem _root_.solution (hθ : IsIndec θ)
  (hα : α < θ) (h : α + β = θ) : β = θ :=
  add_left_cancel (h.trans (hθ.principal.add_eq_right hα).symm)
end IsIndec
end OrdinalStepUp.ErdosRado
