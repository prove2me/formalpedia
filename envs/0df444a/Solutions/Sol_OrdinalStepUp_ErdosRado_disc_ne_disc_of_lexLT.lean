-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.disc_ne_disc_of_lexLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:25.654797+00:00
-- url     : https://prove2.me/submissions/a62fa0f8-d08b-432d-9920-4c7e5d49608a

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
theorem _root_.solution (hab : a ≺ b) (hbc : b ≺ c) : disc a b ≠ disc b c :=
  (· ▸ hab.1 |> hbc.2)
end OrdinalStepUp.ErdosRado
