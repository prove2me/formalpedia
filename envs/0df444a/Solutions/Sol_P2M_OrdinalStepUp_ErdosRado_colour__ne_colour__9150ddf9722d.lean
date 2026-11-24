-- Prove2me | solution 1 for P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:35.364475+00:00
-- url     : https://prove2.me/submissions/e56776ba-961f-4cd0-9298-4b0f6bce9654

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
theorem _root_.solution (hμ : 1 < μ) : colour₀ hμ ≠ colour₁ hμ :=
  fun h => zero_ne_one (congrArg Subtype.val h)
end OrdinalStepUp.ErdosRado
