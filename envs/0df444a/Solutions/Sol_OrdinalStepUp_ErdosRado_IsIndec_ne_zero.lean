-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.IsIndec.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:34.441705+00:00
-- url     : https://prove2.me/submissions/e6a8d541-8849-4075-86b7-576823becb2c

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
theorem _root_.solution (hθ : IsIndec θ) : θ ≠ 0 :=
  fun h0 => absurd (h0 ▸ hθ.one_lt) (by simp)
end IsIndec
end OrdinalStepUp.ErdosRado
