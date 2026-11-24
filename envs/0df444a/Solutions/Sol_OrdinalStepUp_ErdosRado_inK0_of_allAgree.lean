-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.inK0_of_allAgree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:20.694697+00:00
-- url     : https://prove2.me/submissions/5bb8c83f-b5ac-4ddc-abaa-daeb2a27548a

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_agree_iff_lexLT

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (h : AllAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : InK0 u := fun j =>
  have hm : u j.castSucc ≺w u j.succ := u.map_rel_iff.2 (Fin.castSucc_lt_succ (i := j))
  (agree_iff_lexLT hm).1 (h (hu _) (hu _) fun e => irrefl _ (e ▸ hm))
end OrdinalStepUp.ErdosRado
