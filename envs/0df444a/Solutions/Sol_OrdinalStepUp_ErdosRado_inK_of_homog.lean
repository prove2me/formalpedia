-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.inK_of_homog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:59.098414+00:00
-- url     : https://prove2.me/submissions/4b3fa99e-3602-4844-b462-f7693b589fac

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_inK0_of_allAgree
import Theorems.Thm_OrdinalStepUp_ErdosRado_inK1_of_allDisagree

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (h : HomAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : (InK0 ⊔ InK1) u :=
  h.imp (inK0_of_allAgree · hu) (inK1_of_allDisagree · hu)
end OrdinalStepUp.ErdosRado
